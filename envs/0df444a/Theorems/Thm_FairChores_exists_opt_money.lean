-- Prove2me | Theorems.Thm_FairChores_exists_opt_money
-- name    : FairChores.exists_opt_money
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:20:33.747795+00:00
-- url     : https://prove2.me/theorems/729cc3f4-c56d-4631-87ea-2912a985ff76
-- title:
--   Fair Chores: exists opt money
-- statement:
--   For a fixed assignment there is an optimal payment vector.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresMMSPartition.lean#L144-L180
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresMMSPartition.lean#L144-L180

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresMMSPartition
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
omit [DecidableEq T]

theorem FairChores.exists_opt_money (c p : T → ℝ) (hp : ∀ t, 0 ≤ p t) (hn : 0 < n)
    (assign : T → Option (Fin n)) :
    ∃ m : Fin n → ℝ, (∀ j, 0 ≤ m j) ∧ (billOf p assign ≤ ∑ j, m j) ∧
      ∀ m', (∀ j, 0 ≤ m' j) → (billOf p assign ≤ ∑ j, m' j) →
        maxCostData c assign m ≤ maxCostData c assign m' := by sorry
