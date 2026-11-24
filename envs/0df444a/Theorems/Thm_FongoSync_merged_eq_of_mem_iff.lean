-- Prove2me | Theorems.Thm_FongoSync_merged_eq_of_mem_iff
-- name    : FongoSync.merged_eq_of_mem_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:58:13.293288+00:00
-- url     : https://prove2.me/theorems/33092f21-25cb-4ad8-a11b-beac410ef519
-- title:
--   Fongo Sync: merged eq of mem iff
-- statement:
--   **Convergence of the merged state.** Two replicas that applied the same set of changes hold
--   the same state, whatever the order and however often each change arrived.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/State.lean#L151-L158
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/State.lean#L151-L158

import Definitions.Def_FongoSync_Register
import Definitions.Def_FongoSync_State
set_option autoImplicit false
open FongoSync
open Std
set_option linter.unusedSectionVars false
variable {V : Type}
variable [Ord V]
variable [TransOrd V] [LawfulEqOrd V]

theorem FongoSync.merged_eq_of_mem_iff (σ : String → String → Strategy) (cs₁ cs₂ : List (Change V))
    (same : ∀ c, c ∈ cs₁ ↔ c ∈ cs₂) (h : ClockDetermines cs₁) :
    merged σ cs₁ = merged σ cs₂ := by sorry
