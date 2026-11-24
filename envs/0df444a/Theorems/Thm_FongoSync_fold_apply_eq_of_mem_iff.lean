-- Prove2me | Theorems.Thm_FongoSync_fold_apply_eq_of_mem_iff
-- name    : FongoSync.fold_apply_eq_of_mem_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:58:24.765797+00:00
-- url     : https://prove2.me/theorems/adbdb1b8-3a2e-431e-80d8-971e9fd7d467
-- title:
--   Fongo Sync: fold apply eq of mem iff
-- statement:
--   **Register convergence.** A register fed the same set of entries ends the same, whatever the
--   order and however often each arrived, provided clocks are unique.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Register.lean#L400-L407
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Register.lean#L400-L407

import Definitions.Def_FongoSync_Clock
import Batteries.Tactic.Alias
import Definitions.Def_FongoSync_Register
set_option autoImplicit false
open FongoSync
open Std
set_option linter.unusedSectionVars false
variable {V : Type} [Ord V]
variable [TransOrd V] [LawfulEqOrd V]

theorem FongoSync.fold_apply_eq_of_mem_iff (s : Strategy) (l₁ l₂ : List (Entry V))
    (same : ∀ x, x ∈ l₁ ↔ x ∈ l₂) (unique : UniqueClocks l₁) :
    l₁.foldl (apply s) none = l₂.foldl (apply s) none := by sorry
