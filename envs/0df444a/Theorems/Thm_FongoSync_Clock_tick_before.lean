-- Prove2me | Theorems.Thm_FongoSync_Clock_tick_before
-- name    : FongoSync.Clock.tick_before
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:57:13.377829+00:00
-- url     : https://prove2.me/theorems/9a65c4da-9a21-4bc8-98fe-588dc6cb68d0
-- title:
--   Clock: tick before
-- statement:
--   A tick's reading is later than the clock's last reading, whatever `wall` says.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Clock.lean#L115-L120
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Clock.lean#L115-L120

import Definitions.Def_FongoSync_Clock
set_option autoImplicit false
open FongoSync

theorem FongoSync.Clock.tick_before (c : Clock) (wall : Nat) : c.last.Before (c.tick wall).1 := by sorry
