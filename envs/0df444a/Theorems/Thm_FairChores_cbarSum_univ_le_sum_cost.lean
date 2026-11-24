-- Prove2me | Theorems.Thm_FairChores_cbarSum_univ_le_sum_cost
-- name    : FairChores.cbarSum_univ_le_sum_cost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:16:30.151493+00:00
-- url     : https://prove2.me/theorems/bb548ef9-06ff-4377-8a34-f57c962b96a2
-- title:
--   Fair Chores: cbar Sum univ le sum cost
-- statement:
--   The total cost of a feasible outcome is at least the total effective cost of all chores.
--   (This is the manuscript's `n · MMSᵢ ≥ c̄ᵢ(M)`, before taking the infimum.)
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresModel.lean#L134-L150
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresModel.lean#L134-L150

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T]
variable {n : ℕ}
variable {c p : T → ℝ}

theorem FairChores.cbarSum_univ_le_sum_cost {o : Outcome T n} (hvalid : o.Valid p) :
    cbarSum c p Finset.univ ≤ ∑ j, cost c o j := by sorry
