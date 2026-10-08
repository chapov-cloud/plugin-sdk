/*
GTA SA AI World Simulation
C++17 / Win32 / plugin-sdk / Dear ImGui / nlohmann::json

Target:
  GTA San Andreas PC 1.0 US (32-bit) using the matching plugin-sdk GTA SA build.

External source dependencies:
  - plugin-sdk
  - Dear ImGui core + imgui_impl_win32.cpp + imgui_impl_dx9.cpp
  - nlohmann/json.hpp

The plugin deliberately keeps game-thread access to GTA objects on the game
thread. HTTP work is asynchronous and communicates results back through a
mutex-protected queue. No GTA object is touched by the HTTP worker.

Important:
  The plugin-sdk's event addresses are version-specific. This file targets
  the classic 1.0 US layout represented by the current plugin-sdk GTASA event
  definitions. Do not mix it with a different executable/version.
*/

#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <d3d9.h>
#include <winhttp.h>
#include <shellapi.h>

#include <algorithm>
#include <array>
#include <atomic>
#include <chrono>
#include <cmath>
#include <condition_variable>
#include <cstdint>
#include <deque>
#include <mutex>
#include <optional>
#include <sstream>
#include <string>
#include <thread>
#include <unordered_map>
#include <vector>

#pragma comment(lib, "winhttp.lib")

#include "plugin.h"
#include "common.h"
#include "Events.h"
#include "CTimer.h"
#include "CStreaming.h"
#include "CPools.h"
#include "CWorld.h"
#include "CPlayerPed.h"
#include "CPed.h"
#include "CVehicle.h"
#include "CObject.h"
#include "eWeaponType.h"

#include "imgui.h"
#include "imgui_impl_win32.h"
#include "imgui_impl_dx9.h"
#include "json.hpp"

using json = nlohmann::json;
using namespace plugin;

namespace AIWorld {

// ---------------------------------------------------------------------------
// Configuration
// ---------------------------------------------------------------------------

constexpr char kServerHost[] = "127.0.0.1";
constexpr INTERNET_PORT kServerPort = 5000;
constexpr char kPlayerChatPath[] = "/v1/chat/player";
constexpr char kPedChatPath[] = "/v1/chat/peds";

constexpr float CHAT_DISTANCE = 3.0f;
constexpr float AMBUSH_DISTANCE = 15.0f;
constexpr float PED_INTERACTION_DISTANCE = 3.0f;
constexpr int RADAR_PERIOD_FRAMES = 100;
constexpr int MAX_PINS = 10;
constexpr int MAX_LOG_LINES = 15;

static const CVector GROVE_CENTER(-20.7f, -13.3f, 3.1f); // Grove cul-de-sac.

struct ChatLine {
    std::string speaker;
    std::string text;
};

struct NpcState {
    int skin = 0;
    std::string faction = "Civilian";
    std::string uniqueId;
    std::string name;
    bool pinned = false;
};

struct RadarState {
    int playerVehicleModel = 0;
    int playerWeapon = 0;
    std::vector<int> nearbyObjectModels;
    std::vector<int> nearbyPedHandles;
};

struct PendingResult {
    int npcHandle = 0;
    bool pair = false;
    int ped2Handle = 0;
    std::string jsonText;
};

struct Quest {
    bool active = false;
    int targetHandle = 0;
    int targetSkin = 0;
    int reward = 0;
    int blipHandle = 0;
};

static std::mutex g_resultMutex;
static std::deque<PendingResult> g_results;

static std::mutex g_stateMutex;
static std::unordered_map<int, NpcState> g_npcs;
static std::vector<int> g_pins;

static std::vector<ChatLine> g_chat;
static RadarState g_radar;
static Quest g_quest;

static std::atomic<bool> g_running{true};
static std::atomic<bool> g_imguiReady{false};

static bool g_menuOpen = false;
static bool g_chatOpen = false;
static bool g_playerFrozen = false;
static int g_targetHandle = 0;
static int g_selectedNpcHandle = 0;
static int g_playerSkin = 0;
static int g_npcSkinEdit = 0;
static char g_bio[3001] =
    "Clean-slate Los Santos resident. The player is part of an unscripted sandbox world.";
static char g_chatInput[1201] = {};

static WNDPROC g_originalWndProc = nullptr;
static HWND g_gameWindow = nullptr;
static LPDIRECT3DDEVICE9 g_device = nullptr;

// ---------------------------------------------------------------------------
// Small utility layer
// ---------------------------------------------------------------------------

static void Log(const char* msg) {
    OutputDebugStringA("[AIWorld] ");
    OutputDebugStringA(msg);
    OutputDebugStringA("\n");
}

static void PushLog(const std::string& speaker, const std::string& text) {
    if (text.empty()) return;
    g_chat.push_back({speaker, text});
    if (static_cast<int>(g_chat.size()) > MAX_LOG_LINES)
        g_chat.erase(g_chat.begin(), g_chat.begin() + (g_chat.size() - MAX_LOG_LINES));
}

static float Dist2(const CVector& a, const CVector& b) {
    const float dx = a.x - b.x;
    const float dy = a.y - b.y;
    const float dz = a.z - b.z;
    return dx * dx + dy * dy + dz * dz;
}

static std::string EscapeJson(const std::string& s) {
    return json(s).dump();
}

static std::string MakeUniqueId(CPed* ped) {
    if (!ped) return {};
    const int handle = CPools::GetPedRef(ped);
    char buf[64];
    sprintf_s(buf, "ped-%08X", static_cast<unsigned>(handle));
    return buf;
}

static NpcState& StateFor(CPed* ped) {
    const int handle = CPools::GetPedRef(ped);
    auto& state = g_npcs[handle];
    if (state.uniqueId.empty()) {
        state.uniqueId = MakeUniqueId(ped);
        state.skin = ped->m_nModelIndex;
        state.faction = "Civilian";
    }
    return state;
}

// ---------------------------------------------------------------------------
// HTTP client
// ---------------------------------------------------------------------------

static bool HttpPostJson(const std::string& path, const std::string& body,
                         std::string& response) {
    HINTERNET session = WinHttpOpen(
        L"GTA-SA-AI-World/1.0",
        WINHTTP_ACCESS_TYPE_NO_PROXY,
        WINHTTP_NO_PROXY_NAME, WINHTTP_NO_PROXY_BYPASS, 0);
    if (!session) return false;

    WinHttpSetTimeouts(session, 3000, 3000, 45000, 45000);

    HINTERNET connect = WinHttpConnect(session, L"127.0.0.1", kServerPort, 0);
    if (!connect) {
        WinHttpCloseHandle(session);
        return false;
    }

    std::wstring wpath(path.begin(), path.end());
    HINTERNET request = WinHttpOpenRequest(
        connect, L"POST", wpath.c_str(), nullptr, WINHTTP_NO_REFERER,
        WINHTTP_DEFAULT_ACCEPT_TYPES, 0);

    if (!request) {
        WinHttpCloseHandle(connect);
        WinHttpCloseHandle(session);
        return false;
    }

    const wchar_t* headers = L"Content-Type: application/json\r\n";
    BOOL ok = WinHttpSendRequest(
        request, headers, static_cast<DWORD>(-1L),
        const_cast<char*>(body.data()), static_cast<DWORD>(body.size()),
        static_cast<DWORD>(body.size()), 0);

    if (ok) ok = WinHttpReceiveResponse(request, nullptr);

    if (ok) {
        std::string data;
        DWORD available = 0;
        do {
            available = 0;
            if (!WinHttpQueryDataAvailable(request, &available) || available == 0)
                break;
            std::string chunk(available, '\0');
            DWORD read = 0;
            if (!WinHttpReadData(request, chunk.data(), available, &read))
                break;
            chunk.resize(read);
            data += chunk;
        } while (available > 0);
        response = std::move(data);
    }

    WinHttpCloseHandle(request);
    WinHttpCloseHandle(connect);
    WinHttpCloseHandle(session);
    return ok == TRUE;
}

static void AsyncPost(const std::string& path, const json& payload,
                      int npcHandle, int ped2Handle = 0) {
    std::string body = payload.dump();
    std::thread([body, path, npcHandle, ped2Handle]() {
        std::string response;
        if (!HttpPostJson(path, body, response)) {
            Log("HTTP request failed; is server.py running?");
            return;
        }
        std::lock_guard<std::mutex> lock(g_resultMutex);
        g_results.push_back({npcHandle, ped2Handle != 0, ped2Handle, response});
    }).detach();
}

// ---------------------------------------------------------------------------
// Player / ped helpers
// ---------------------------------------------------------------------------

static CPed* PedFromHandle(int handle) {
    if (!handle) return nullptr;
    CPed* ped = CPools::GetPed(handle);
    return ped && ped->IsPointerValid() ? ped : nullptr;
}

static void FreezePed(CPed* ped, bool freeze) {
    if (!ped) return;
    if (freeze) {
        ped->SetPedState(PEDSTATE_IDLE);
        ped->SetMoveState(PEDMOVE_NONE);
    } else {
        ped->SetPedState(PEDSTATE_IDLE);
    }
}

static void FreezePlayer(bool freeze) {
    CPlayerPed* player = FindPlayerPed(0);
    if (!player) return;
    g_playerFrozen = freeze;

    // Keep the pad neutral rather than modifying global keyboard state.
    // GTA will therefore see no movement/fire/jump input while typing.
    if (freeze) {
        if (CPad* pad = player->GetPadFromPlayer()) {
            pad->Clear(false, true);
        }
        player->SetMoveState(PEDMOVE_NONE);
    }
}

static int GetWeaponId(CPed* ped) {
    if (!ped) return 0;
    return static_cast<int>(ped->GetWeapon()->m_eWeaponType);
}

static CPed* FindNearestPed(float radius) {
    CPlayerPed* player = FindPlayerPed(0);
    if (!player) return nullptr;

    const CVector origin = player->GetPosition();
    CPed* best = nullptr;
    float bestD2 = radius * radius;

    for (auto ped : CPools::ms_pPedPool) {
        if (!ped || ped == player || !ped->IsPointerValid()) continue;
        const float d2 = Dist2(origin, ped->GetPosition());
        if (d2 < bestD2) {
            best = ped;
            bestD2 = d2;
        }
    }
    return best;
}

static CPed* FindAimedPed() {
    CPlayerPed* player = FindPlayerPed(0);
    if (!player) return nullptr;
    // Plugin-SDK exposes the selected target on CPlayerPed. If the target is
    // outside the pool or invalid, fall back to proximity.
    CPed* target = player->m_pPlayerTargettedPed;
    if (target && target->IsPointerValid()) return target;
    return FindNearestPed(8.0f);
}

// ---------------------------------------------------------------------------
// Model changes
// ---------------------------------------------------------------------------

static bool SetPedModel(CPed* ped, int modelId) {
    if (!ped || modelId < 0 || modelId > 311) return false;

    CStreaming::RequestModel(modelId, 2);
    CStreaming::LoadAllRequestedModels(false);

    ped->SetModelIndex(modelId);
    CStreaming::SetModelIsDeletable(modelId);
    return true;
}

static void ApplyPlayerSkin() {
    CPlayerPed* player = FindPlayerPed(0);
    if (player) SetPedModel(player, g_playerSkin);
}

static void ApplyNpcSkin(CPed* ped, int skin) {
    if (!ped) return;
    if (SetPedModel(ped, skin)) {
        auto& state = StateFor(ped);
        state.skin = skin;
    }
}

// ---------------------------------------------------------------------------
// Pins
// ---------------------------------------------------------------------------

static void PinNpc(CPed* ped) {
    if (!ped) return;
    const int handle = CPools::GetPedRef(ped);
    if (std::find(g_pins.begin(), g_pins.end(), handle) != g_pins.end())
        return;
    if (static_cast<int>(g_pins.size()) >= MAX_PINS) return;

    // CPed::bDontRenderOnScreen is not a persistence mechanism. The robust
    // gameplay-side solution is to make the ped a real population ped and keep
    // a reference to it. This SDK exposes ConvertToRealPed through population
    // internals only on selected builds, so this plugin keeps the pin cap and
    // hard reference here without fabricating an unsupported symbol.
    auto& state = StateFor(ped);
    state.pinned = true;
    g_pins.push_back(handle);
}

static void UnpinNpc(CPed* ped) {
    if (!ped) return;
    const int handle = CPools::GetPedRef(ped);
    g_pins.erase(std::remove(g_pins.begin(), g_pins.end(), handle), g_pins.end());
    auto it = g_npcs.find(handle);
    if (it != g_npcs.end()) it->second.pinned = false;
}

// ---------------------------------------------------------------------------
// Radar
// ---------------------------------------------------------------------------

static void ScanRadar() {
    CPlayerPed* player = FindPlayerPed(0);
    if (!player) return;

    g_radar = {};
    if (CVehicle* vehicle = FindPlayerVehicle(0, false))
        g_radar.playerVehicleModel = vehicle->m_nModelIndex;
    g_radar.playerWeapon = GetWeaponId(player);

    const CVector p = player->GetPosition();
    constexpr float radius = 30.0f;
    const float r2 = radius * radius;

    // Ped pool is the cheap, reliable proximity source. We deliberately do not
    // walk every world object here because the scan runs only once per 100
    // frames and object-pool iteration can be large.
    for (auto ped : CPools::ms_pPedPool) {
        if (!ped || ped == player || !ped->IsPointerValid()) continue;
        if (Dist2(p, ped->GetPosition()) <= r2) {
            g_radar.nearbyPedHandles.push_back(CPools::GetPedRef(ped));
        }
    }

    // Static/dynamic world objects: cap at 32 so the context payload remains
    // bounded even in object-dense interiors.
    for (auto object : CPools::ms_pObjectPool) {
        if (!object) continue;
        if (Dist2(p, object->GetPosition()) <= r2) {
            g_radar.nearbyObjectModels.push_back(object->m_nModelIndex);
            if (g_radar.nearbyObjectModels.size() >= 32) break;
        }
    }
}

// ---------------------------------------------------------------------------
// Ambush / ambient faction simulation
// ---------------------------------------------------------------------------

static std::string FactionForSkin(int skin) {
    if (skin >= 102 && skin <= 104) return "Ballas";
    if (skin >= 105 && skin <= 107) return "Grove Street Families";
    if (skin >= 114 && skin <= 116) return "Los Santos Vagos";
    if (skin >= 117 && skin <= 118) return "Varrios Los Aztecas";
    if (skin >= 120 && skin <= 125) return "Syndicate";
    if (skin >= 126 && skin <= 138) return "Law Enforcement";
    return "Civilian";
}

static bool HostileFaction(const std::string& a, const std::string& b) {
    if (a == b || a == "Civilian" || b == "Civilian") return false;
    if ((a == "Ballas" && b == "Grove Street Families") ||
        (b == "Ballas" && a == "Grove Street Families")) return true;
    if ((a == "Los Santos Vagos" && b == "Varrios Los Aztecas") ||
        (b == "Los Santos Vagos" && a == "Varrios Los Aztecas")) return true;
    if ((a == "Syndicate" && b == "Law Enforcement") ||
        (b == "Syndicate" && a == "Law Enforcement")) return true;
    return false;
}

static void StartAttack(CPed* attacker, CPed* target, int weapon) {
    if (!attacker || !target || !attacker->IsPointerValid() ||
        !target->IsPointerValid()) return;

    if (weapon > 0) {
        attacker->GiveWeapon(static_cast<eWeaponType>(weapon), 250, true);
        attacker->SetCurrentWeapon(static_cast<eWeaponType>(weapon));
    }

    // eObjective is represented by TASK-like high-level ped objectives in
    // plugin-sdk. ForceStoredObjective is intentionally avoided here because
    // task constructors differ between SDK revisions; the direct CPed method
    // below is the stable engine primitive for this build.
    attacker->SetObjective(OBJECTIVE_KILL_CHAR_ON_FOOT, target);
}

static void RunFactionRadar() {
    CPlayerPed* player = FindPlayerPed(0);
    if (!player) return;

    const int playerSkin = player->m_nModelIndex;
    const std::string playerFaction = FactionForSkin(playerSkin);

    // Player-vs-faction ambush.
    if (playerFaction != "Civilian") {
        for (int handle : g_radar.nearbyPedHandles) {
            CPed* ped = PedFromHandle(handle);
            if (!ped) continue;
            const std::string faction = FactionForSkin(ped->m_nModelIndex);
            if (HostileFaction(playerFaction, faction) &&
                Dist2(player->GetPosition(), ped->GetPosition()) <=
                    AMBUSH_DISTANCE * AMBUSH_DISTANCE) {
                StartAttack(ped, player, GetWeaponId(ped));
            }
        }
    }

    // NPC-vs-NPC contact.
    for (size_t i = 0; i < g_radar.nearbyPedHandles.size(); ++i) {
        CPed* a = PedFromHandle(g_radar.nearbyPedHandles[i]);
        if (!a) continue;
        for (size_t j = i + 1; j < g_radar.nearbyPedHandles.size(); ++j) {
            CPed* b = PedFromHandle(g_radar.nearbyPedHandles[j]);
            if (!b) continue;
            if (Dist2(a->GetPosition(), b->GetPosition()) >
                PED_INTERACTION_DISTANCE * PED_INTERACTION_DISTANCE)
                continue;

            const std::string fa = FactionForSkin(a->m_nModelIndex);
            const std::string fb = FactionForSkin(b->m_nModelIndex);
            if (!HostileFaction(fa, fb)) continue;

            FreezePed(a, true);
            FreezePed(b, true);

            json payload = {
                {"ped1_skin_id", a->m_nModelIndex},
                {"ped2_skin_id", b->m_nModelIndex},
                {"ped1_unique_id", StateFor(a).uniqueId},
                {"ped2_unique_id", StateFor(b).uniqueId},
                {"distance_m", std::sqrt(Dist2(a->GetPosition(), b->GetPosition()))},
                {"ped1_context", "Two ambient NPCs have encountered each other."},
                {"ped2_context", "Two ambient NPCs have encountered each other."},
                {"nearby_objects", g_radar.nearbyObjectModels}
            };
            AsyncPost(kPedChatPath, payload,
                      CPools::GetPedRef(a), CPools::GetPedRef(b));
            return; // prevent request storms during this frame.
        }
    }
}

// ---------------------------------------------------------------------------
// Server response application
// ---------------------------------------------------------------------------

static void ApplyAction(CPed* npc, const json& r) {
    if (!npc) return;
    const std::string action = r.value("action", "IDLE");
    const int weapon = r.value("weapon_id", 0);

    if (action == "LAUGH") {
        npc->SetPedState(PEDSTATE_IDLE);
    } else if (action == "HANDS_UP") {
        npc->SetPedState(PEDSTATE_FLEE_ENTITY);
    } else if (action == "WANDER_FLEE") {
        npc->SetPedState(PEDSTATE_FLEE_ENTITY);
    } else if (action == "GIVE_WEAPON_AND_ATTACK") {
        CPed* player = FindPlayerPed(0);
        StartAttack(npc, player, weapon);
    } else if (action == "TRIGGER_FACTION_WAR") {
        // Faction warfare is evaluated by the radar on the next cycle.
        if (weapon > 0) {
            npc->GiveWeapon(static_cast<eWeaponType>(weapon), 250, true);
            npc->SetCurrentWeapon(static_cast<eWeaponType>(weapon));
        }
    }
}

static void ApplyResults() {
    std::deque<PendingResult> local;
    {
        std::lock_guard<std::mutex> lock(g_resultMutex);
        local.swap(g_results);
    }

    for (const auto& result : local) {
        CPed* npc = PedFromHandle(result.npcHandle);
        if (!npc) continue;

        try {
            json r = json::parse(result.jsonText);

            if (!result.pair) {
                PushLog("NPC", r.value("text", ""));
                ApplyAction(npc, r);

                if (r.value("action", "") == "START_QUEST") {
                    g_quest.active = true;
                    g_quest.targetSkin = r.value("target_skin_id", 0);
                    g_quest.reward = r.value("reward_money", 0);

                    // Target selection is resolved on the game thread.
                    for (auto ped : CPools::ms_pPedPool) {
                        if (ped && ped->m_nModelIndex == g_quest.targetSkin &&
                            ped != FindPlayerPed(0)) {
                            g_quest.targetHandle = CPools::GetPedRef(ped);
                            break;
                        }
                    }
                }
            } else {
                CPed* ped2 = PedFromHandle(result.ped2Handle);
                if (!ped2) continue;

                PushLog("NPC-1", r.value("ped1_text", ""));
                PushLog("NPC-2", r.value("ped2_text", ""));

                json a = {
                    {"action", r.value("ped1_action", "IDLE")},
                    {"weapon_id", r.value("ped1_weapon", 0)}
                };
                json b = {
                    {"action", r.value("ped2_action", "IDLE")},
                    {"weapon_id", r.value("ped2_weapon", 0)}
                };

                ApplyAction(npc, a);
                ApplyAction(ped2, b);
                FreezePed(npc, false);
                FreezePed(ped2, false);
            }
        } catch (const std::exception& e) {
            Log(e.what());
            FreezePed(npc, false);
        }
    }
}

// ---------------------------------------------------------------------------
// Player chat
// ---------------------------------------------------------------------------

static void SendPlayerChat() {
    CPed* npc = PedFromHandle(g_targetHandle);
    CPlayerPed* player = FindPlayerPed(0);
    if (!npc || !player) {
        g_chatOpen = false;
        FreezePlayer(false);
        return;
    }

    std::string message(g_chatInput);
    if (message.empty()) return;

    auto& state = StateFor(npc);
    CVehicle* vehicle = FindPlayerVehicle(0, false);

    json payload = {
        {"player_message", message},
        {"player_skin_id", player->m_nModelIndex},
        {"player_description", std::string(g_bio)},
        {"npc_skin_id", npc->m_nModelIndex},
        {"npc_unique_id", state.uniqueId},
        {"player_vehicle_id", vehicle ? vehicle->m_nModelIndex : 0},
        {"nearby_objects", g_radar.nearbyObjectModels},
        {"nearby_peds", json::array()}
    };

    for (int handle : g_radar.nearbyPedHandles) {
        CPed* nearby = PedFromHandle(handle);
        if (!nearby) continue;
        payload["nearby_peds"].push_back({
            {"handle", handle},
            {"skin_id", nearby->m_nModelIndex},
            {"weapon_id", GetWeaponId(nearby)},
            {"distance_m", std::sqrt(Dist2(player->GetPosition(), nearby->GetPosition()))}
        });
    }

    PushLog("PLAYER", message);
    AsyncPost(kPlayerChatPath, payload, CPools::GetPedRef(npc));

    g_chatInput[0] = '\0';
    g_chatOpen = false;
    FreezePlayer(false);
    FreezePed(npc, false);
}

static void OpenChat() {
    CPed* npc = FindNearestPed(CHAT_DISTANCE);
    if (!npc) return;
    g_targetHandle = CPools::GetPedRef(npc);
    g_chatOpen = true;
    FreezePlayer(true);
    FreezePed(npc, true);
    SetCursorPos(0, 0);
}

// ---------------------------------------------------------------------------
// Mission/story sandbox
// ---------------------------------------------------------------------------

static void ConfigureSandbox() {
    CPlayerPed* player = FindPlayerPed(0);
    if (!player) return;

    // Story missions and cutscenes are script-owned systems. The plugin avoids
    // binary patches into SCM code and instead continuously restores the
    // sandbox invariants on the game thread.
    player->SetWantedLevelNoDrop(0);

    if (Dist2(player->GetPosition(), GROVE_CENTER) > 250.0f) {
        player->Teleport(GROVE_CENTER);
    }

    // The stock wanted-system can be reasserted by scripts; zeroing it here
    // makes border crossings safe in the sandbox. The actual zone geometry
    // remains GTA's native world geometry.
}

static void EnsureInitialSpawn() {
    static bool done = false;
    if (done) return;

    CPlayerPed* player = FindPlayerPed(0);
    if (!player) return;

    player->Teleport(GROVE_CENTER);
    player->SetWantedLevelNoDrop(0);
    done = true;
}

// ---------------------------------------------------------------------------
// ImGui integration
// ---------------------------------------------------------------------------

static LRESULT CALLBACK WndProc(HWND hwnd, UINT msg, WPARAM wParam, LPARAM lParam) {
    if (g_imguiReady && ImGui_ImplWin32_WndProcHandler(hwnd, msg, wParam, lParam))
        return TRUE;
    return CallWindowProc(g_originalWndProc, hwnd, msg, wParam, lParam);
}

static bool InitImGui() {
    if (g_imguiReady) return true;
    g_device = reinterpret_cast<LPDIRECT3DDEVICE9>(GetD3DDevice());
    if (!g_device) return false;

    g_gameWindow = FindWindowA(nullptr, "GTA: San Andreas");
    if (!g_gameWindow) g_gameWindow = GetForegroundWindow();
    if (!g_gameWindow) return false;

    g_originalWndProc = reinterpret_cast<WNDPROC>(
        SetWindowLongPtrA(g_gameWindow, GWLP_WNDPROC,
            reinterpret_cast<LONG_PTR>(WndProc)));

    IMGUI_CHECKVERSION();
    ImGui::CreateContext();
    ImGuiIO& io = ImGui::GetIO();
    io.ConfigFlags |= ImGuiConfigFlags_NavEnableKeyboard;
    ImGui::StyleColorsDark();

    if (!ImGui_ImplWin32_Init(g_gameWindow) ||
        !ImGui_ImplDX9_Init(g_device)) {
        return false;
    }

    g_imguiReady = true;
    return true;
}

static void ShutdownImGui() {
    if (!g_imguiReady) return;
    ImGui_ImplDX9_Shutdown();
    ImGui_ImplWin32_Shutdown();
    ImGui::DestroyContext();

    if (g_originalWndProc && g_gameWindow)
        SetWindowLongPtrA(g_gameWindow, GWLP_WNDPROC,
            reinterpret_cast<LONG_PTR>(g_originalWndProc));

    g_originalWndProc = nullptr;
    g_gameWindow = nullptr;
    g_imguiReady = false;
}

static void DrawProfileTab() {
    ImGui::TextUnformatted("Clean-slate player profile");
    ImGui::InputTextMultiline("Biography / roleplay context", g_bio,
                              sizeof(g_bio), ImVec2(-1, 120));

    ImGui::Separator();
    ImGui::SliderInt("Player Skin ID", &g_playerSkin, 0, 311);
    if (ImGui::Button("Apply player skin"))
        ApplyPlayerSkin();

    ImGui::Text("Current vehicle model: %d", g_radar.playerVehicleModel);
    ImGui::Text("Current weapon: %d", g_radar.playerWeapon);
}

static void DrawNpcTab() {
    ImGui::Text("Targeted/nearby NPC");
    CPed* target = PedFromHandle(g_selectedNpcHandle);
    if (target) {
        auto& state = StateFor(target);
        ImGui::Text("Handle: %d", g_selectedNpcHandle);
        ImGui::Text("Unique ID: %s", state.uniqueId.c_str());

        g_npcSkinEdit = state.skin;
        if (ImGui::SliderInt("NPC Skin ID", &g_npcSkinEdit, 0, 311)) {
            ApplyNpcSkin(target, g_npcSkinEdit);
        }

        bool pinned = state.pinned;
        if (ImGui::Checkbox("Pin NPC (max 10)", &pinned)) {
            if (pinned) PinNpc(target);
            else UnpinNpc(target);
        }
    } else {
        ImGui::TextUnformatted("No valid NPC selected.");
    }

    ImGui::Separator();
    ImGui::BeginChild("chat", ImVec2(0, 220), true);
    for (const auto& line : g_chat)
        ImGui::TextWrapped("[%s] %s", line.speaker.c_str(), line.text.c_str());
    ImGui::EndChild();
}

static void DrawChatPopup() {
    if (!g_chatOpen) return;

    ImGui::SetNextWindowSize(ImVec2(520, 150), ImGuiCond_Always);
    ImGui::Begin("NPC Conversation", &g_chatOpen,
                 ImGuiWindowFlags_NoCollapse | ImGuiWindowFlags_NoResize);
    ImGui::TextUnformatted("You are typing. Player controls are frozen.");
    ImGui::InputTextMultiline("##chat", g_chatInput, sizeof(g_chatInput),
                              ImVec2(-1, 60),
                              ImGuiInputTextFlags_EnterReturnsTrue);
    if (ImGui::IsItemDeactivatedAfterEdit())
        SendPlayerChat();

    if (ImGui::Button("Send"))
        SendPlayerChat();
    ImGui::SameLine();
    if (ImGui::Button("Cancel")) {
        g_chatOpen = false;
        g_chatInput[0] = '\0';
        FreezePlayer(false);
        FreezePed(PedFromHandle(g_targetHandle), false);
    }
    ImGui::End();
}

static void DrawMenu() {
    if (!g_menuOpen) return;

    ImGui::SetNextWindowSize(ImVec2(700, 560), ImGuiCond_FirstUseEver);
    ImGui::Begin("GTA SA AI World Simulation", &g_menuOpen);
    if (ImGui::BeginTabBar("tabs")) {
        if (ImGui::BeginTabItem("Player Profile")) {
            DrawProfileTab();
            ImGui::EndTabItem();
        }
        if (ImGui::BeginTabItem("NPC Customizer & Chat Log")) {
            DrawNpcTab();
            ImGui::EndTabItem();
        }
        ImGui::EndTabBar();
    }
    ImGui::End();

    DrawChatPopup();
}

// ---------------------------------------------------------------------------
// Event callbacks
// ---------------------------------------------------------------------------

static void OnGameProcess() {
    static int frameCounter = 0;
    ++frameCounter;

    EnsureInitialSpawn();
    ConfigureSandbox();
    ApplyResults();

    if (KeyPressed(VK_F7)) {
        g_menuOpen = !g_menuOpen;
        if (g_menuOpen) InitImGui();
    }

    if (!g_menuOpen && !g_chatOpen && KeyPressed('T'))
        OpenChat();

    if (g_menuOpen) {
        CPed* aimed = FindAimedPed();
        if (aimed) g_selectedNpcHandle = CPools::GetPedRef(aimed);
    }

    if (frameCounter % RADAR_PERIOD_FRAMES == 0) {
        ScanRadar();
        RunFactionRadar();
    }

    // Quest completion is checked cheaply on the game thread.
    if (g_quest.active) {
        CPed* target = PedFromHandle(g_quest.targetHandle);
        if (!target) {
            // Handle no longer resolves => ped is dead/despawned. In a real
            // production build this should additionally check death state;
            // CPed pool invalidation is used here to avoid dereferencing
            // destroyed entities.
            if (CPlayerPed* player = FindPlayerPed(0)) {
                CWorld::Players[0].m_nMoney += g_quest.reward;
                CWorld::Players[0].m_nDisplayMoney = CWorld::Players[0].m_nMoney;
            }
            g_quest = {};
        }
    }
}

static void OnDrawing() {
    if (!g_imguiReady) {
        if (!InitImGui()) return;
    }

    ImGui_ImplDX9_NewFrame();
    ImGui_ImplWin32_NewFrame();
    ImGui::NewFrame();

    DrawMenu();

    ImGui::Render();
    ImGui_ImplDX9_RenderDrawData(ImGui::GetDrawData());
}

static void OnD3DReset() {
    if (g_imguiReady)
        ImGui_ImplDX9_InvalidateDeviceObjects();
}

static void OnInitGame() {
    // The sandbox is configured lazily because player pools are not guaranteed
    // to exist at the exact init callback.
    Log("GTA SA AI World Simulation initialized.");
}

// ---------------------------------------------------------------------------
// Plugin entry point
// ---------------------------------------------------------------------------

class AIWorldPlugin {
public:
    AIWorldPlugin() {
        Events::initGameEvent += [] { OnInitGame(); };
        Events::gameProcessEvent += [] { OnGameProcess(); };
        Events::drawingEvent += [] { OnDrawing(); };
        Events::d3dResetEvent += [] { OnD3DReset(); };
    }

    ~AIWorldPlugin() {
        g_running = false;
        ShutdownImGui();
    }
};

static AIWorldPlugin g_plugin;

} // namespace AIWorld
