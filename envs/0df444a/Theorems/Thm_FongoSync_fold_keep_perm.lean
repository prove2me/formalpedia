-- Prove2me | Theorems.Thm_FongoSync_fold_keep_perm
-- name    : FongoSync.fold_keep_perm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:02:38.226947+00:00
-- url     : https://prove2.me/theorems/301e5115-73ac-4a8f-b95a-9b2404c6299d
-- title:
--   Fongo Sync: fold keep perm
-- statement:
--   The Fongo Sync construction uses the fold keep perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Register.lean#L241-L243
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Register.lean#L241-L243

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

theorem FongoSync.fold_keep_perm {l₁ l₂ : List E} (p : l₁.Perm l₂) (inj : KeyInj key l₁) (h : Option E) :
    l₁.foldl (keep cmp key) h = l₂.foldl (keep cmp key) h := by sorry
