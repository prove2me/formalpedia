-- Prove2me | Theorems.Thm_FongoSync_Clock_observe_then_tick
-- name    : FongoSync.Clock.observe_then_tick
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:59:50.15403+00:00
-- url     : https://prove2.me/theorems/38903cd8-5a33-4578-ab26-a6f6f05e8ffb
-- title:
--   Clock: observe then tick
-- statement:
--   The next tick after observing an encodable reading is later than it.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Clock.lean#L149-L152
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Clock.lean#L149-L152

import Definitions.Def_FongoSync_Clock
set_option autoImplicit false
open FongoSync

theorem FongoSync.Clock.observe_then_tick (c : Clock) (remote : Hlc) (wall : Nat)
    (h : remote.encodable) : remote < ((c.observe remote).tick wall).1 := by sorry
