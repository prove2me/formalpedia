-- Prove2me | Theorems.Thm_FongoSync_Laws_tick_after_observe
-- name    : FongoSync.Laws.tick_after_observe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:05:26.799072+00:00
-- url     : https://prove2.me/theorems/4c1f74fe-ab3f-4147-96bc-5a8e1ce05b40
-- title:
--   Laws: tick after observe
-- statement:
--   The next tick after observing an encodable reading is later than it.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Laws.lean#L31-L33
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Laws.lean#L31-L33

import Definitions.Def_FongoSync_Examples
import Definitions.Def_FongoSync_Model
import Definitions.Def_FongoSync_Run
import Definitions.Def_FongoSync_Laws
set_option autoImplicit false
open FongoSync FongoSync.Laws
open FongoSync

theorem FongoSync.Laws.tick_after_observe (c : Clock) (remote : Hlc) (wall : Nat) (h : remote.encodable) :
    remote < ((c.observe remote).tick wall).1 := by sorry
