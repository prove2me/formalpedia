-- Prove2me | Theorems.Thm_FongoSync_merge_comm
-- name    : FongoSync.merge_comm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:59:13.477979+00:00
-- url     : https://prove2.me/theorems/4bcf4a08-0115-48f5-9fe7-a5303e924528
-- title:
--   Fongo Sync: merge comm
-- statement:
--   The Fongo Sync construction uses the merge comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Register.lean#L383-L389
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Register.lean#L383-L389

import Definitions.Def_FongoSync_Clock
import Batteries.Tactic.Alias
import Definitions.Def_FongoSync_Register
set_option autoImplicit false
open FongoSync
open Std
set_option linter.unusedSectionVars false
variable {V : Type} [Ord V]
variable [TransOrd V] [LawfulEqOrd V]

theorem FongoSync.merge_comm (s : Strategy) (a b : Option (Entry V))
    (unique : ∀ x ∈ a, ∀ y ∈ b, x.clock = y.clock → x = y) :
    merge s a b = merge s b a := by sorry
