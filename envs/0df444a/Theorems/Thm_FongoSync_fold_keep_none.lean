-- Prove2me | Theorems.Thm_FongoSync_fold_keep_none
-- name    : FongoSync.fold_keep_none
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:00:17.210982+00:00
-- url     : https://prove2.me/theorems/33a85238-301c-45a2-874c-26158edc634f
-- title:
--   Fongo Sync: fold keep none
-- statement:
--   The Fongo Sync construction uses the fold keep none property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Register.lean#L203-L211
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Register.lean#L203-L211

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

theorem FongoSync.fold_keep_none (l : List E) (h : Option E) :
    l.foldl (keep cmp key) h = none ↔ h = none ∧ l = [] := by sorry
