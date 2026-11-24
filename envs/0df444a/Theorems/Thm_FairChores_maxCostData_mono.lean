-- Prove2me | Theorems.Thm_FairChores_maxCostData_mono
-- name    : FairChores.maxCostData_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:20:29.026286+00:00
-- url     : https://prove2.me/theorems/cdf4c68c-edaa-48f9-8c02-cf3e96242641
-- title:
--   Fair Chores: max Cost Data mono
-- statement:
--   `maxCostData` is monotone in the payment vector.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresMMSPartition.lean#L95-L97
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresMMSPartition.lean#L95-L97

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresMMSPartition
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
omit [DecidableEq T]

theorem FairChores.maxCostData_mono (c : T → ℝ) (assign : T → Option (Fin n)) {m m' : Fin n → ℝ}
    (h : ∀ j, m j ≤ m' j) : maxCostData c assign m ≤ maxCostData c assign m' := by sorry
