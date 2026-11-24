-- Prove2me | Theorems.Thm_FongoSync_Clock_tick_last
-- name    : FongoSync.Clock.tick_last
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:59:44.545618+00:00
-- url     : https://prove2.me/theorems/fdca7c7a-fd7d-4009-a1a2-4b132292faa4
-- title:
--   Clock: tick last
-- statement:
--   The clock remembers the reading it issued.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Clock.lean#L126-L126
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Clock.lean#L126-L126

import Definitions.Def_FongoSync_Clock
set_option autoImplicit false
open FongoSync

theorem FongoSync.Clock.tick_last (c : Clock) (wall : Nat) : (c.tick wall).2.last = (c.tick wall).1 := by sorry
