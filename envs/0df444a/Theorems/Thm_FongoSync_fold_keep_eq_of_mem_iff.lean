-- Prove2me | Theorems.Thm_FongoSync_fold_keep_eq_of_mem_iff
-- name    : FongoSync.fold_keep_eq_of_mem_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:58:20.398628+00:00
-- url     : https://prove2.me/theorems/8ed6924b-44c4-4d06-b9c5-9ad6eca9d6b6
-- title:
--   Fongo Sync: fold keep eq of mem iff
-- statement:
--   **Set invariance.** Folding from nothing depends only on which entries the list holds: not
--   their order, and not how often each appears.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Register.lean#L215-L239
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Register.lean#L215-L239

import Definitions.Def_FongoSync_Clock
import Batteries.Tactic.Alias
import Definitions.Def_FongoSync_Register
set_option autoImplicit false
open FongoSync
open Std
set_option linter.unusedSectionVars false
variable {E K : Type} (cmp : K → K → Ordering) (key : E → K)
variable [TransCmp cmp] [LawfulEqCmp cmp]
variable {cmp key}

theorem FongoSync.fold_keep_eq_of_mem_iff (l₁ l₂ : List E) (same : ∀ x, x ∈ l₁ ↔ x ∈ l₂)
    (inj : KeyInj key l₁) :
    l₁.foldl (keep cmp key) none = l₂.foldl (keep cmp key) none := by sorry
