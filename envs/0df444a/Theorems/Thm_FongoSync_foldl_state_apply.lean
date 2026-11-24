-- Prove2me | Theorems.Thm_FongoSync_foldl_state_apply
-- name    : FongoSync.foldl_state_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:00:24.243691+00:00
-- url     : https://prove2.me/theorems/2ec89864-87dc-4d5b-a0eb-eba67aa01306
-- title:
--   Fongo Sync: foldl state apply
-- statement:
--   The Fongo Sync construction uses the foldl state apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/State.lean#L68-L78
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/State.lean#L68-L78

import Definitions.Def_FongoSync_Register
import Definitions.Def_FongoSync_State
set_option autoImplicit false
open FongoSync
open Std
set_option linter.unusedSectionVars false
variable {V : Type}
variable [Ord V]

theorem FongoSync.foldl_state_apply (σ : String → String → Strategy) (cs : List (Change V)) (st : State V)
    (k : Key) :
    (cs.foldl (State.apply σ) st) k = (entriesAt cs k).foldl (apply (strategyAt σ k)) (st k) := by sorry
