-- Prove2me | Theorems.Thm_FairChores_maxCost_le_iff
-- name    : FairChores.maxCost_le_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:20:19.391442+00:00
-- url     : https://prove2.me/theorems/71fbc0e9-bb71-45f3-884a-aedcbf302fd5
-- title:
--   Fair Chores: max Cost le iff
-- statement:
--   The Fair Chores construction uses the max Cost le iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresMMSPartition.lean#L38-L41
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresMMSPartition.lean#L38-L41

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresMMSPartition
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
omit [Fintype T] [DecidableEq T]

theorem FairChores.maxCost_le_iff (hn : 0 < n) (c : T → ℝ) (o : Outcome T n) (r : ℝ) :
    maxCost c o ≤ r ↔ ∀ j, cost c o j ≤ r := by sorry
