-- Prove2me | Theorems.Thm_FairChores_maxCost_assignOutcome
-- name    : FairChores.maxCost_assignOutcome
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:20:35.094643+00:00
-- url     : https://prove2.me/theorems/aed54aa8-172d-4789-8dc1-adeea8eabaf6
-- title:
--   Fair Chores: max Cost assign Outcome
-- statement:
--   The Fair Chores construction uses the max Cost assign Outcome property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresMMSPartition.lean#L74-L75
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresMMSPartition.lean#L74-L75

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresMMSPartition
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
omit [DecidableEq T]

theorem FairChores.maxCost_assignOutcome (c : T → ℝ) (assign : T → Option (Fin n)) (m : Fin n → ℝ) :
    maxCost c (assignOutcome assign m) = maxCostData c assign m := by sorry
