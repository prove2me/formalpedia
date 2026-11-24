-- Prove2me | Theorems.Thm_FongoSync_Clock_tick_lt
-- name    : FongoSync.Clock.tick_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:59:42.962147+00:00
-- url     : https://prove2.me/theorems/c0a226ee-ec3b-4f27-b63d-bccf90a005e5
-- title:
--   Clock: tick lt
-- statement:
--   The Clock construction uses the tick lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Clock.lean#L122-L123
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Clock.lean#L122-L123

import Definitions.Def_FongoSync_Clock
set_option autoImplicit false
open FongoSync

theorem FongoSync.Clock.tick_lt (c : Clock) (wall : Nat) : c.last < (c.tick wall).1 := by sorry
