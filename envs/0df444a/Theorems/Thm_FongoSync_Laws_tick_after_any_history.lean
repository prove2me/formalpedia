-- Prove2me | Theorems.Thm_FongoSync_Laws_tick_after_any_history
-- name    : FongoSync.Laws.tick_after_any_history
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:05:28.811308+00:00
-- url     : https://prove2.me/theorems/c0566979-b351-494b-a693-2edb9bbb4b02
-- title:
--   Laws: tick after any history
-- statement:
--   After any history, the next tick is later than the start, than every reading issued, and
--   than every encodable reading observed.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Laws.lean#L37-L40
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Laws.lean#L37-L40

import Definitions.Def_FongoSync_Examples
import Definitions.Def_FongoSync_Model
import Definitions.Def_FongoSync_Run
import Definitions.Def_FongoSync_Laws
import Theorems.Thm_FongoSync_Clock_tick_after_any_history

set_option autoImplicit false
open FongoSync FongoSync.Laws
open FongoSync

theorem FongoSync.Laws.tick_after_any_history (c : Clock) (events : List Event) (wall : Nat) :
    c.last < ((c.run events).1.tick wall).1 ∧
      ∀ r ∈ (c.run events).2, r < ((c.run events).1.tick wall).1 := by sorry
