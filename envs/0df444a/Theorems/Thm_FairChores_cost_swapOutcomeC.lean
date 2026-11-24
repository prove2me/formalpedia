-- Prove2me | Theorems.Thm_FairChores_cost_swapOutcomeC
-- name    : FairChores.cost_swapOutcomeC
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:21:37.072867+00:00
-- url     : https://prove2.me/theorems/4469fb8f-d17e-408b-9248-f55e55147edd
-- title:
--   Fair Chores: cost swap Outcome C
-- statement:
--   The Fair Chores construction uses the cost swap Outcome C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresTwoAgents.lean#L235-L236
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresTwoAgents.lean#L235-L236

import Mathlib
import Definitions.Def_RequestProject_ChoresMMSPartition
import Definitions.Def_RequestProject_ChoresPreAlloc
import Definitions.Def_RequestProject_ChoresTwoAgents
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T]
omit [Fintype T] [DecidableEq T]

theorem FairChores.cost_swapOutcomeC (c : T → ℝ) (o : Outcome T 2) (j : Fin 2) :
    cost c (swapOutcomeC o) j = cost c o (Equiv.swap 0 1 j) := by sorry
