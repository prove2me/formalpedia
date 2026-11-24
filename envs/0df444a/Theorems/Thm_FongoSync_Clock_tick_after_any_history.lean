-- Prove2me | Theorems.Thm_FongoSync_Clock_tick_after_any_history
-- name    : FongoSync.Clock.tick_after_any_history
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:57:16.121964+00:00
-- url     : https://prove2.me/theorems/ce5d66da-5de0-4c4b-82ee-639207db3b18
-- title:
--   Clock: tick after any history
-- statement:
--   **The clock law.** After any history of ticks and observations, the next tick is later than
--   the clock's starting point, than every reading it issued, and than every encodable reading it
--   observed, whatever wall time it is given.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Clock.lean#L205-L211
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Clock.lean#L205-L211

import Definitions.Def_FongoSync_Clock
set_option autoImplicit false
open FongoSync

theorem FongoSync.Clock.tick_after_any_history (c : Clock) (events : List Event) (wall : Nat) :
    c.last < ((c.run events).1.tick wall).1 ∧
      ∀ r ∈ (c.run events).2, r < ((c.run events).1.tick wall).1 := by sorry
