-- Prove2me | Theorems.Thm_FairChores_exists_assignform_le
-- name    : FairChores.exists_assignform_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:20:41.5408+00:00
-- url     : https://prove2.me/theorems/8d9b93a6-5df7-4017-93ae-2ff0ba873d91
-- title:
--   Fair Chores: exists assignform le
-- statement:
--   Every feasible outcome can be re-expressed in assignment form without increasing its
--   worst-part cost.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresMMSPartition.lean#L184-L238
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresMMSPartition.lean#L184-L238

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresMMSPartition
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}

theorem FairChores.exists_assignform_le (hn : 0 < n) (c p : T → ℝ) (o : Outcome T n) (ho : o.Valid p) :
    ∃ (assign : T → Option (Fin n)) (m : Fin n → ℝ),
      (∀ j, 0 ≤ m j) ∧ (billOf p assign ≤ ∑ j, m j) ∧
      maxCostData c assign m ≤ maxCost c o := by sorry
