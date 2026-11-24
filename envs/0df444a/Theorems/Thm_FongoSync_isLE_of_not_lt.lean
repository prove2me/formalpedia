-- Prove2me | Theorems.Thm_FongoSync_isLE_of_not_lt
-- name    : FongoSync.isLE_of_not_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:59:02.652814+00:00
-- url     : https://prove2.me/theorems/71217bb8-0c92-43d2-b474-d3b24c62d881
-- title:
--   Fongo Sync: is LE of not lt
-- statement:
--   The Fongo Sync construction uses the is LE of not lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Register.lean#L121-L125
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Register.lean#L121-L125

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

theorem FongoSync.isLE_of_not_lt {x y : K} (h : cmp x y ≠ .lt) : (cmp y x).isLE := by sorry
