-- Prove2me | Theorems.Thm_FongoSync_fold_keep_dup
-- name    : FongoSync.fold_keep_dup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:02:40.978717+00:00
-- url     : https://prove2.me/theorems/ce5dac20-8ae1-4ebf-8cf6-af5c23528f3c
-- title:
--   Fongo Sync: fold keep dup
-- statement:
--   The Fongo Sync construction uses the fold keep dup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Register.lean#L245-L247
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Register.lean#L245-L247

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

theorem FongoSync.fold_keep_dup (l : List E) (inj : KeyInj key l) :
    (l ++ l).foldl (keep cmp key) none = l.foldl (keep cmp key) none := by sorry
