-- Prove2me | Theorems.Thm_FongoSync_apply_lww_clock
-- name    : FongoSync.apply_lww_clock
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:00:25.079861+00:00
-- url     : https://prove2.me/theorems/c9d2df31-7d41-46e3-96a6-fa58f5404bd7
-- title:
--   Fongo Sync: apply lww clock
-- statement:
--   Under `Lww` a register ends at the later of the two clocks.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Register.lean#L359-L367
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Register.lean#L359-L367

import Definitions.Def_FongoSync_Clock
import Batteries.Tactic.Alias
import Definitions.Def_FongoSync_Register
set_option autoImplicit false
open FongoSync
open Std
set_option linter.unusedSectionVars false
variable {V : Type} [Ord V]
variable [TransOrd V] [LawfulEqOrd V]

theorem FongoSync.apply_lww_clock (held e : Entry V) :
    (apply .lww (some held) e).map (·.clock) =
      some (if held.clock < e.clock then e.clock else held.clock) := by sorry
