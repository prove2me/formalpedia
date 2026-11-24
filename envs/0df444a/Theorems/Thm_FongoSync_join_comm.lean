-- Prove2me | Theorems.Thm_FongoSync_join_comm
-- name    : FongoSync.join_comm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:00:10.039807+00:00
-- url     : https://prove2.me/theorems/fcb0e07d-c94d-401a-aa46-66cdcbeb6878
-- title:
--   Fongo Sync: join comm
-- statement:
--   The Fongo Sync construction uses the join comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Register.lean#L100-L109
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Register.lean#L100-L109

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

theorem FongoSync.join_comm (a b : Option E) (inj : ∀ x ∈ a, ∀ y ∈ b, key x = key y → x = y) :
    join cmp key a b = join cmp key b a := by sorry
