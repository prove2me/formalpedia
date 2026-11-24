-- Prove2me | Theorems.Thm_FongoSync_trichotomy
-- name    : FongoSync.trichotomy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:02:33.124024+00:00
-- url     : https://prove2.me/theorems/90e8ef08-7e94-438a-86b1-6c8c9907c9a9
-- title:
--   Fongo Sync: trichotomy
-- statement:
--   The Fongo Sync construction uses the trichotomy property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Register.lean#L114-L119
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Register.lean#L114-L119

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

theorem FongoSync.trichotomy {x y : E} (inj : key x = key y → x = y) :
    cmp (key x) (key y) = .lt ∨ x = y ∨ cmp (key y) (key x) = .lt := by sorry
