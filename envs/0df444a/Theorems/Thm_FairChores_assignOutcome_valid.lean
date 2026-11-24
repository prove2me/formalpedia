-- Prove2me | Theorems.Thm_FairChores_assignOutcome_valid
-- name    : FairChores.assignOutcome_valid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:20:36.758798+00:00
-- url     : https://prove2.me/theorems/a97595ff-443a-44ff-a5ac-4c539c412676
-- title:
--   Fair Chores: assign Outcome valid
-- statement:
--   Feasibility of `assignOutcome`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresMMSPartition.lean#L118-L140
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresMMSPartition.lean#L118-L140

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresMMSPartition
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}

theorem FairChores.assignOutcome_valid (p : T → ℝ) (assign : T → Option (Fin n)) (m : Fin n → ℝ)
    (hm0 : ∀ j, 0 ≤ m j) (hms : billOf p assign ≤ ∑ j, m j) :
    (assignOutcome assign m).Valid p := by sorry
