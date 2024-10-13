#include <chrono>
#include <unordered_set>
#include <windows.h>
//
#include <SokuLib.hpp>
#include <cstdint>
#include <dinput.h>
//
#include <atomic>
#include <iostream>
#include <iterator>
#include <map>
#include <mutex>
#include <optional>
#include <shared_mutex>
#include <vector>
//
#include "BattleMode.hpp"
#include "DrawUtils.hpp"
#include "Key.hpp"
#include "NetObject.hpp"
#include "Packet.hpp"
#include "Scenes.hpp"
#include "SokuAddresses.hpp"
#include "Tamper.hpp"
#include "VTables.hpp"
#include "Vector2.hpp"
#include "libloaderapi.h"
#include "memoryapi.h"
#include "minwindef.h"
#include "processthreadsapi.h"
#include "winbase.h"
#include "winerror.h"
#include "winnt.h"
#include "winsock.h"
#include <psapi.h>
#include <shlwapi.h>

static bool init = false;
static void (SokuLib::BattleManager::*ogBattleMgrOnRender)();
static SokuLib::DrawUtils::Sprite text_cif_on;
static SokuLib::DrawUtils::Sprite text_cif_off;
static SokuLib::DrawUtils::Sprite text_cif_unknown;
static int selectTextP1X;
static int selectTextP1Y;
static int selectTextP2X;
static int selectTextP2Y;
static int battleTextP1X;
static int battleTextP1Y;
static int battleTextP2X;
static int battleTextP2Y;
static int battleTextX;
static int battleTextY;
static unsigned int cifOnColor;
static unsigned int cifOffColor;
static unsigned int cifUnknownColor;

static std::atomic_bool preference;
static int switchKey;
SokuLib::Vector2i selectCifIndicatorPosition[2];
// SokuLib::Vector2i battleCifIndicatorPosition[2];
static HMODULE cif;

// We check if the game version is what we target (in our case, Soku 1.10a).
extern "C" __declspec(dllexport) bool CheckVersion(const BYTE hash[16]) {
  return memcmp(hash, SokuLib::targetHash, sizeof(SokuLib::targetHash)) == 0;
}

struct CiF {
  char *address;
  size_t size;
  std::vector<char> backup;
  std::vector<char> cif_hooked;
  static CiF from_memory(char *addr, size_t size) {
    return CiF{addr, size, std::vector<char>(addr, addr + size)};
  }
  void save_hooked() {
    this->cif_hooked = std::vector<char>(this->address, this->address + size);
  }
  void hook() const {
    DWORD old;
    VirtualProtect(this->address, this->size, PAGE_EXECUTE_READWRITE, &old);
    memcpy(this->address, this->cif_hooked.data(), this->size);
    VirtualProtect(this->address, this->size, old, &old);
  }
  void unhook() const {
    DWORD old;
    VirtualProtect(this->address, this->size, PAGE_EXECUTE_READWRITE, &old);
    memcpy(this->address, this->backup.data(), this->size);
    VirtualProtect(this->address, this->size, old, &old);
  }
};

static std::map<char *, CiF> cifHookMap;
void hook() {
  for (auto i = cifHookMap.begin(); i != cifHookMap.end(); i++)
    i->second.hook();
  FlushInstructionCache(GetCurrentProcess(), nullptr, 0);
  std::cout << "hook CiF" << std::endl;
}
void unhook() {
  for (auto i = cifHookMap.rbegin(); i != cifHookMap.rend(); i++)
    i->second.unhook();
  FlushInstructionCache(GetCurrentProcess(), nullptr, 0);
  std::cout << "unhook CiF" << std::endl;
}

struct CifStatus {
  std::optional<bool> status;
  char to_char() const {
    return this->status.has_value() ? this->status.value() : -1;
  }
  SokuLib::DrawUtils::Sprite &to_text() const {
    if (!this->status.has_value())
      return text_cif_unknown;
    return this->status.value() ? text_cif_on : text_cif_off;
  }
  CifStatus(char v) {
    if (v < 0)
      this->status = {};
    else
      this->status = v;
  }
  CifStatus() = default;
  bool operator==(CifStatus r) const { return this->status == r.status; }
  bool operator!=(CifStatus r) const { return this->status != r.status; }
};

static std::atomic_bool render = true;
static std::atomic_bool switchByKey = true;
static std::atomic_bool exchangeViaSocket = true;
static std::shared_mutex battleModeMutex;
static std::optional<SokuLib::BattleMode> lastBattleMode;
void initializeTexts() {
  static bool textsInitialized = false;
  if (textsInitialized)
    return;
  SokuLib::SWRFont font;
  SokuLib::FontDescription desc;
  // white
  desc.r2 = 255;
  desc.g2 = 255;
  desc.b2 = 255;
  desc.height = 17;
  desc.weight = FW_BOLD;
  desc.italic = 0;
  desc.shadow = 4;
  desc.bufferSize = 1000000;
  desc.charSpaceX = 0;
  desc.charSpaceY = 0;
  desc.offsetX = 0;
  desc.offsetY = 0;
  desc.useOffset = 0;
  strcpy(desc.faceName, "MonoSpatialModSWR");
  font.create();

  SokuLib::Vector2i realSize;

  // green
  desc.r1 = (cifOnColor & 0xff0000) >> 16;
  desc.g1 = (cifOnColor & 0x00ff00) >> 8;
  desc.b1 = (cifOnColor & 0x0000ff);
  font.setIndirect(desc);
  text_cif_on.texture.createFromText("CiF on", font, {150, 50}, &realSize);
  text_cif_on.setSize(realSize.to<unsigned>());
  text_cif_on.rect.width = realSize.x;
  text_cif_on.rect.height = realSize.y;

  // red
  desc.r1 = (cifOffColor & 0xff0000) >> 16;
  desc.g1 = (cifOffColor & 0x00ff00) >> 8;
  desc.b1 = (cifOffColor & 0x0000ff);
  font.setIndirect(desc);
  text_cif_off.texture.createFromText("CiF off", font, {150, 50}, &realSize);
  text_cif_off.setSize(realSize.to<unsigned>());
  text_cif_off.rect.width = realSize.x;
  text_cif_off.rect.height = realSize.y;

  // yellow
  desc.r1 = (cifUnknownColor & 0xff0000) >> 16;
  desc.g1 = (cifUnknownColor & 0x00ff00) >> 8;
  desc.b1 = (cifUnknownColor & 0x0000ff);
  // black
  desc.r2 = 0;
  desc.g2 = 0;
  desc.b2 = 0;
  font.setIndirect(desc);
  text_cif_unknown.texture.createFromText("CiF unknown", font, {150, 50},
                                          &realSize);
  text_cif_unknown.setSize(realSize.to<unsigned>());
  text_cif_unknown.rect.width = realSize.x;
  text_cif_unknown.rect.height = realSize.y;

  font.destruct();
  textsInitialized = true;
}
static std::atomic<CifStatus> playersCiF[2];
extern "C" __declspec(dllexport) void setRender(bool enableRender) {
  render = enableRender;
}
extern "C" __declspec(dllexport) void setSwitchByKey(bool enable) {
  switchByKey = enable;
}
extern "C" __declspec(dllexport) void setExchangeViaSocket(bool enable) {
  exchangeViaSocket = enable;
}

extern "C" __declspec(dllexport) bool setSelfCifStatus(bool status) {
  status ? hook() : unhook();
  return preference.exchange(status);
}

extern "C" __declspec(dllexport) bool getSelfCifStatus() { return preference; }
extern "C" __declspec(dllexport) char getPlayerCifStatus(bool p2) {
  return playersCiF[p2].load().to_char();
}
extern "C" __declspec(dllexport) char setPlayerCifStatus(bool p2, char v) {
  return playersCiF[p2].exchange(CifStatus(v)).to_char();
}

bool checkKey(unsigned char scancode) { return ((char *)0x8a01b8)[scancode]; }
bool checkNoModKeys() {
  return !checkKey(DIK_LALT) && !checkKey(DIK_RALT) &&
         !GetAsyncKeyState(VK_MENU) && !GetAsyncKeyState(VK_LWIN) &&
         !GetAsyncKeyState(VK_RWIN);
}
bool checkSwitchKey() {
  static bool noModifierKeyPressed = checkNoModKeys();
  const bool pressed = switchKey && checkKey(switchKey);
  if (pressed)
    return noModifierKeyPressed;
  noModifierKeyPressed = checkNoModKeys();
  return false;
}

static std::atomic<std::chrono::system_clock::time_point> othersChangedTime;
static std::chrono::system_clock::duration selectOthersChangedDuration;
static std::chrono::system_clock::duration battleOthersChangedDuration;
static std::atomic<std::chrono::system_clock::time_point> selfCifChangedTime;
static std::chrono::system_clock::duration selfCifChangedDuration;

template <int(WINAPI *const *oriRecvfrom)(
    SOCKET s, char *buf, int len, int flags, SOCKADDR *from, int *fromlen)>
int WINAPI myRecvfrom(SOCKET s, char *buf, int len, int flags, SOCKADDR *from,
                      int *fromlen) {
  int ret = (*oriRecvfrom)(s, buf, len, flags, from, fromlen);
  if (exchangeViaSocket && ret >= 3 && buf[0] == 'C') {
    std::shared_lock<std::shared_mutex> _lock(battleModeMutex);
    bool changed = false;
    if (!lastBattleMode.has_value())
      return ret;
    switch (lastBattleMode.value()) {
    case SokuLib::BATTLE_MODE_VSCLIENT: // as server
      changed = playersCiF[1].exchange(buf[2]) != CifStatus(buf[2]);
      break;
    case SokuLib::BATTLE_MODE_VSSERVER: // as client
      changed = playersCiF[0].exchange(buf[1]) != CifStatus(buf[1]);
      break;
    case SokuLib::BATTLE_MODE_VSWATCH: { // spectator
      changed = playersCiF[1].exchange(buf[2]) != CifStatus(buf[2]);
      changed |= playersCiF[0].exchange(buf[1]) != CifStatus(buf[1]);
      break;
    }
    default:
      break;
    }
    if (changed)
      othersChangedTime = std::chrono::system_clock::now();
  }
  return ret;
}

template <int(WINAPI *const *oriSendto)(SOCKET s, const char *buf, int len,
                                        int flags, const SOCKADDR *to,
                                        int tolen)>
int WINAPI mySendto(SOCKET s, const char *buf, int len, int flags,
                    const SOCKADDR *to, int tolen) {
  if (exchangeViaSocket && len >= 1 + 1 + 4 + 1) {
    SokuLib::Packet *packet = ((SokuLib::Packet *)buf);
    switch (packet->type) {
    case SokuLib::HOST_GAME:
    case SokuLib::CLIENT_GAME:
      switch (packet->game.event.type) {
      case SokuLib::GAME_INPUT:
        if (packet->game.event.input.sceneId ==
            SokuLib::SCENEID_CHARACTER_SELECT) {
          char buf[] = {'C', playersCiF[0].load().to_char(),
                        playersCiF[1].load().to_char()};
          (*oriSendto)(s, buf, sizeof(buf), flags, to, tolen);
        }
        break;
      case SokuLib::GAME_REPLAY: {
        // static auto replay = SokuLib::DPP_REPLAY();
        // replay.decode(&packet->game.event);
        // size_t end = replay.frameId + 1;
        // size_t start = end - replay.inputs.size() / 2;
        // std::cout << start << " " << end << std::endl;
        // // send CiF status at the beginning of a battle and every 300 frames.
        // if (start < 120 || end / 300 > start / 300) {
        char buf[] = {'C', playersCiF[0].load().to_char(),
                      playersCiF[1].load().to_char()};
        (*oriSendto)(s, buf, sizeof(buf), flags, to, tolen);
        // }
      }
      default:;
      }
    default:;
    }
  }
  return (*oriSendto)(s, buf, len, flags, to, tolen);
}

void drawOnPosition(SokuLib::DrawUtils::Sprite &text, int x, int y) {
  text.setPosition(
      SokuLib::Vector2i{x - text.rect.width / 2, y - text.rect.height / 2});
  text.draw();
}

template <class T, int (T::*const *ogBattleOnRender)()>
int __fastcall myBattleOnRender(T *This) {
  // std::cout << (int)playersCiF[0].load().to_char() << " "
  //           << (int)playersCiF[1].load().to_char() << std::endl;
  int ret = (This->**ogBattleOnRender)();
  if (!render)
    return ret;
  auto now = std::chrono::system_clock::now();
  if (now - othersChangedTime.load() > battleOthersChangedDuration &&
      now - selfCifChangedTime.load() > selfCifChangedDuration)
    return ret;
  if (SokuLib::mainMode == SokuLib::BATTLE_MODE_VSSERVER ||
      SokuLib::mainMode == SokuLib::BATTLE_MODE_VSCLIENT ||
      SokuLib::mainMode == SokuLib::BATTLE_MODE_VSWATCH) {
    drawOnPosition(playersCiF[0].load().to_text(), battleTextP1X,
                   battleTextP1Y);
    drawOnPosition(playersCiF[1].load().to_text(), battleTextP2X,
                   battleTextP2Y);
  }
  drawOnPosition(CifStatus(preference.load()).to_text(), battleTextX,
                 battleTextY);
  return ret;
}

template <class T, int (T::*const *ogSelectOnRender)()>
int __fastcall mySelectOnRender(T *This) {
  // std::cout << (int)playersCiF[0].load().to_char() << " "
  //           << (int)playersCiF[1].load().to_char() << std::endl;
  int ret = (This->**ogSelectOnRender)();
  if (!render)
    return ret;
  if (*(int *)((char *)This + 0x4f60) >= 0) // if selecting stage
    return ret;
  auto now = std::chrono::system_clock::now();
  if (now - othersChangedTime.load() > selectOthersChangedDuration &&
      now - selfCifChangedTime.load() > selfCifChangedDuration)
    return ret;
  drawOnPosition(playersCiF[0].load().to_text(), selectTextP1X, selectTextP1Y);
  drawOnPosition(playersCiF[1].load().to_text(), selectTextP2X, selectTextP2Y);
  return ret;
}

static bool lastPress;
template <class T, int (T::*const *ogBattleOnProcess)()>
int __fastcall myBattleOnProcess(T *This) {
  initializeTexts();
  int ret = (This->**ogBattleOnProcess)();
  bool isNetplay = SokuLib::mainMode == SokuLib::BATTLE_MODE_VSSERVER ||
                   SokuLib::mainMode == SokuLib::BATTLE_MODE_VSCLIENT;
  {
    std::lock_guard<std::shared_mutex> _lock(battleModeMutex);
    if (ret != SokuLib::sceneId) {
      lastBattleMode = {};
      return ret;
    }
    if (!lastBattleMode.has_value()) {
      othersChangedTime = std::chrono::system_clock::now();
      if (!isNetplay)
        playersCiF[0] = playersCiF[1] = CifStatus();
    }
    lastBattleMode = SokuLib::mainMode;
  }
  bool status = preference;
  if (checkSwitchKey()) {
    selfCifChangedTime = std::chrono::system_clock::now();
    if (!lastPress) {
      if (!isNetplay) {
        lastPress = true;
        status = !status;
        preference = status;
        status ? hook() : unhook();
      }
    }
  } else
    lastPress = false;
  return ret;
}

template <class T, int (T::*const *ogSelectOnProcess)()>
int __fastcall mySelectOnProcess(T *This) {
  initializeTexts();
  int ret = (This->**ogSelectOnProcess)();
  {
    std::lock_guard<std::shared_mutex> _lock(battleModeMutex);
    if (ret != SokuLib::sceneId) {
      lastBattleMode = {};
      return ret;
    }
    if (!lastBattleMode.has_value()) {
      othersChangedTime = std::chrono::system_clock::now();
      playersCiF[0] = playersCiF[1] = CifStatus();
    }
    lastBattleMode = SokuLib::mainMode;
  }
  bool status = preference;
  if (checkSwitchKey()) {
    selfCifChangedTime = std::chrono::system_clock::now();
    if (!lastPress) {
      auto This_ = (SokuLib::Select *)This;
      lastPress = true;
      std::cout << (int)SokuLib::mainMode << " "
                << (int)This_->leftSelectionStage << " "
                << (int)This_->rightSelectionStage << std::endl;
      do {
        switch (SokuLib::mainMode) {
        case SokuLib::BATTLE_MODE_VSCLIENT: // as server
          if (This_->leftSelectionStage >= 3)
            continue;
          break;
        case SokuLib::BATTLE_MODE_VSSERVER: // as client
          if (This_->rightSelectionStage >= 3)
            continue;
          break;
        default:
          if (This_->leftSelectionStage >= 3 &&
              This_->rightSelectionStage >= 3) {
            continue;
          }
        }
        status = !status;
        preference = status;
        status ? hook() : unhook();
      } while (0);
    }
  } else
    lastPress = false;
  switch (SokuLib::mainMode) {
  case SokuLib::BATTLE_MODE_VSCLIENT: // as server
    playersCiF[0] = status;
    break;
  case SokuLib::BATTLE_MODE_VSSERVER: // as client
    playersCiF[1] = status;
    break;
  default: // local
    playersCiF[0] = playersCiF[1] = status;
  }
  return ret;
}

static std::atomic<std::optional<DWORD>> threadId;
BOOL(WINAPI *ogVirtualProtect)
(LPVOID lpAddress, SIZE_T dwSize, DWORD flNewProtect,
 PDWORD lpflOldProtect) = VirtualProtect;

BOOL WINAPI myVirtualProtect(LPVOID lpAddress, SIZE_T dwSize,
                             DWORD flNewProtect, PDWORD lpflOldProtect) {
  if (0x00400000 <= (size_t)lpAddress && (size_t)lpAddress <= 0x008a343b &&
      GetCurrentThreadId() == threadId.load()) {
    char *addr = (char *)lpAddress;
    if (cifHookMap.find(addr) == cifHookMap.end()) {
      cifHookMap[addr] = CiF::from_memory(addr, dwSize);
    } else {
      assert(cifHookMap[addr].cif_hooked.size() == 0 &&
             cifHookMap[addr].size == dwSize);
      cifHookMap[addr].save_hooked();
    }
  }
  return ogVirtualProtect(lpAddress, dwSize, flNewProtect, lpflOldProtect);
}

template <void (*const *oriDrawCharacters)()>
void drawHitCountersAfterDrawCharacters() {
  (*oriDrawCharacters)();
  auto DrawHitCounter = (void(__fastcall *)(void *This))0x00478e30;
  // draw p1 hits counter
  DrawHitCounter(*(char **)0x8985e8 + 0x16c);
  DrawHitCounter(*(char **)0x8985e8 + 0x1a0);
  // draw p2 hits counter
}

// Called when the mod loader is ready to initialize this module.
// All hooks should be placed here. It's also a good moment to load settings
// from the ini.
extern "C" __declspec(dllexport) bool Initialize(HMODULE hMyModule,
                                                 HMODULE hParentModule) {
  wchar_t path[1024 + MAX_PATH];
  GetModuleFileNameW(hMyModule, path, 1024);
  PathRemoveFileSpecW(path);
  PathAppendW(path, L"CharactersInForeground.ini");
  preference =
      GetPrivateProfileIntW(L"Preference", L"activate_cif_by_default", 0, path);
  switchKey =
      GetPrivateProfileIntW(L"KeyBinding", L"toggle_cif", DIK_TAB, path);
  selectTextP1X = GetPrivateProfileIntW(L"Texts", L"select_p1_x", 385, path);
  selectTextP1Y = GetPrivateProfileIntW(L"Texts", L"select_p1_y", 150, path);
  selectTextP2X = GetPrivateProfileIntW(L"Texts", L"select_p2_x", 385, path);
  selectTextP2Y = GetPrivateProfileIntW(L"Texts", L"select_p2_y", 439, path);
  battleTextP1X = GetPrivateProfileIntW(L"Texts", L"battle_p1_x", 140, path);
  battleTextP1Y = GetPrivateProfileIntW(L"Texts", L"battle_p1_y", 67, path);
  battleTextP2X = GetPrivateProfileIntW(L"Texts", L"battle_p2_x", 500, path);
  battleTextP2Y = GetPrivateProfileIntW(L"Texts", L"battle_p2_y", 67, path);
  battleTextX = GetPrivateProfileIntW(L"Texts", L"battle_self_x", 320, path);
  battleTextY = GetPrivateProfileIntW(L"Texts", L"battle_self_y", 120, path);
  cifOnColor = GetPrivateProfileIntW(L"Texts", L"cif_on_color", 0x00ff00, path);
  cifOffColor =
      GetPrivateProfileIntW(L"Texts", L"cif_off_color", 0xff0000, path);
  cifUnknownColor =
      GetPrivateProfileIntW(L"Texts", L"cif_unknown_color", 0xffff00, path);
  selectOthersChangedDuration = std::chrono::seconds(GetPrivateProfileIntW(
      L"DisplayDuration", L"opponent_cif_toggled", 0xffffffff, path));
  battleOthersChangedDuration = std::chrono::seconds(
      GetPrivateProfileIntW(L"DisplayDuration", L"enter_battle", 2, path));
  selfCifChangedDuration = std::chrono::seconds(
      GetPrivateProfileIntW(L"DisplayDuration", L"self_cif_toggleed", 2, path));
  bool hitCounterInForeground =
      GetPrivateProfileIntW(L"Tweak", L"hit_counter_in_foreground", 1, path);
  PathRemoveFileSpecW(path);
  PathAppendW(path, L"CharactersInForeground-original.dat");
  cif = LoadLibraryExW(path, NULL, 0);
  assert(cif != 0);
  auto init = (bool (*)(HMODULE))GetProcAddress(cif, "Initialize");
  assert(init != 0);
  MODULEINFO moduleinfo;
  GetModuleInformation(GetCurrentProcess(), cif, &moduleinfo,
                       sizeof(moduleinfo));
  const auto pp_VirtualProtect =
      (BOOL(WINAPI **)(LPVOID, SIZE_T, DWORD, PDWORD))(
          (unsigned char *)moduleinfo.lpBaseOfDll + (0x1000f018u - 0x10000000));
  DWORD old;
  VirtualProtect(pp_VirtualProtect, 4, PAGE_EXECUTE_READWRITE, &old);
  ogVirtualProtect = SokuLib::TamperDword(pp_VirtualProtect, myVirtualProtect);
  threadId = GetCurrentThreadId();
  init(hMyModule);
  threadId.store({});
  SokuLib::TamperDword(pp_VirtualProtect, ogVirtualProtect);
  VirtualProtect(pp_VirtualProtect, 4, old, &old);
  std::unordered_set<char *> bytes;
  for (auto i = cifHookMap.begin(); i != cifHookMap.end(); i++) {
    if (i->second.cif_hooked.size() == 0)
      i->second.save_hooked();
    for (char *a = i->second.address; a < i->second.address + i->second.size;
         a++) {
      assert(bytes.find(a) == bytes.end());
      bytes.insert(a);
    }
  }
  VirtualProtect((PVOID)RDATA_SECTION_OFFSET, RDATA_SECTION_SIZE,
                 PAGE_EXECUTE_READWRITE, &old);
  // hook Select OnProcess
  static int (SokuLib::SelectClient::*const ogSelectClientOnProcess)() =
      SokuLib::TamperDword(
          &SokuLib::VTable_SelectClient.onProcess,
          mySelectOnProcess<SokuLib::SelectClient, &ogSelectClientOnProcess>);
  static int (SokuLib::SelectServer::*const ogSelectServerOnProcess)() =
      SokuLib::TamperDword(
          &SokuLib::VTable_SelectServer.onProcess,
          mySelectOnProcess<SokuLib::SelectServer, &ogSelectServerOnProcess>);
  static int (SokuLib::Select::*const ogSelectOnProcess)() =
      SokuLib::TamperDword(
          &SokuLib::VTable_Select.onProcess,
          mySelectOnProcess<SokuLib::Select, &ogSelectOnProcess>);
  // hook Select OnRender
  static int (SokuLib::SelectClient::*const ogSelectClientOnRender)() =
      SokuLib::TamperDword(
          &SokuLib::VTable_SelectClient.onRender,
          mySelectOnRender<SokuLib::SelectClient, &ogSelectClientOnRender>);
  static int (SokuLib::SelectServer::*const ogSelectServerOnRender)() =
      SokuLib::TamperDword(
          &SokuLib::VTable_SelectServer.onRender,
          mySelectOnRender<SokuLib::SelectServer, &ogSelectServerOnRender>);
  static int (SokuLib::Select::*const ogSelectOnRender)() =
      SokuLib::TamperDword(
          &SokuLib::VTable_Select.onRender,
          mySelectOnRender<SokuLib::Select, &ogSelectOnRender>);
  // hook Battle OnProcess
  static int (SokuLib::Battle::*const ogBattleOnProcess)() =
      SokuLib::TamperDword(
          &SokuLib::VTable_Battle.onProcess,
          myBattleOnProcess<SokuLib::Battle, &ogBattleOnProcess>);
  static int (SokuLib::BattleClient::*const ogBattleClientOnProcess)() =
      SokuLib::TamperDword(
          &SokuLib::VTable_BattleClient.onProcess,
          myBattleOnProcess<SokuLib::BattleClient, &ogBattleClientOnProcess>);
  static int (SokuLib::BattleServer::*const ogBattleServerOnProcess)() =
      SokuLib::TamperDword(
          &SokuLib::VTable_BattleServer.onProcess,
          myBattleOnProcess<SokuLib::BattleServer, &ogBattleServerOnProcess>);
  static int (SokuLib::BattleWatch::*const ogBattleWatchOnProcess)() =
      SokuLib::TamperDword(
          &SokuLib::VTable_BattleWatch.onProcess,
          myBattleOnProcess<SokuLib::BattleWatch, &ogBattleWatchOnProcess>);
  // hook Battle OnRender
  static int (SokuLib::Battle::*const ogBattleOnRender)() =
      SokuLib::TamperDword(
          &SokuLib::VTable_Battle.onRender,
          myBattleOnRender<SokuLib::Battle, &ogBattleOnRender>);
  static int (SokuLib::BattleWatch::*const ogBattleWatchOnRender)() =
      SokuLib::TamperDword(
          &SokuLib::VTable_BattleWatch.onRender,
          myBattleOnRender<SokuLib::BattleWatch, &ogBattleWatchOnRender>);
  static int (SokuLib::BattleServer::*const ogBattleServerOnRender)() =
      SokuLib::TamperDword(
          &SokuLib::VTable_BattleServer.onRender,
          myBattleOnRender<SokuLib::BattleServer, &ogBattleServerOnRender>);
  static int (SokuLib::BattleClient::*const ogBattleClientOnRender)() =
      SokuLib::TamperDword(
          &SokuLib::VTable_BattleClient.onRender,
          myBattleOnRender<SokuLib::BattleClient, &ogBattleClientOnRender>);
  VirtualProtect((PVOID)RDATA_SECTION_OFFSET, RDATA_SECTION_SIZE, old, &old);
  VirtualProtect((PVOID)TEXT_SECTION_OFFSET, TEXT_SECTION_SIZE,
                 PAGE_EXECUTE_READWRITE, &old);
  static int(WINAPI *const oriRecvfrom)(SOCKET, char *, int, int, SOCKADDR *,
                                        int *) =
      SokuLib::TamperNearCall(0x0041dae5, myRecvfrom<&oriRecvfrom>);
  static int(WINAPI *const oriSendto)(
      SOCKET s, const char *buf, int len, int flags, const SOCKADDR *to,
      int tolen) = SokuLib::TamperNearCall(0x004171cd, mySendto<&oriSendto>);
  VirtualProtect((PVOID)TEXT_SECTION_OFFSET, TEXT_SECTION_SIZE, old, &old);
  if (!preference) {
    unhook();
  }
  if (hitCounterInForeground) {
    MODULEINFO moduleinfo;
    GetModuleInformation(GetCurrentProcess(), cif, &moduleinfo,
                         sizeof(moduleinfo));
    const auto cif_call_draw_characters =
        (unsigned char *)moduleinfo.lpBaseOfDll + (0x10001a23 - 0x10000000);
    assert(*cif_call_draw_characters == 0xe8);
    DWORD old;
    VirtualProtect(cif_call_draw_characters, 5, PAGE_EXECUTE_READWRITE, &old);
    static void (*const oriDrawCharacters)() = SokuLib::TamperNearCall(
        (DWORD)cif_call_draw_characters,
        drawHitCountersAfterDrawCharacters<&oriDrawCharacters>);
    VirtualProtect(cif_call_draw_characters, 5, old, &old);
  }
  FlushInstructionCache(GetCurrentProcess(), nullptr, 0);
  std::atomic_thread_fence(std::memory_order_release);
  return true;
}

extern "C" int APIENTRY DllMain(HMODULE hModule, DWORD fdwReason,
                                LPVOID lpReserved) {
  return TRUE;
}

// New mod loader functions
// Loading priority. Mods are loaded in order by ascending level of priority
// (the highest first). When 2 mods define the same loading priority the loading
// order is undefined.
extern "C" __declspec(dllexport) int getPriority() { return -1; }

// Not yet implemented in the mod loader, subject to change
// SokuModLoader::IValue **getConfig();
// void freeConfig(SokuModLoader::IValue **v);
// bool commitConfig(SokuModLoader::IValue *);
// const char *getFailureReason();
// bool hasChainedHooks();
// void unHook();
