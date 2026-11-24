-- Prove2me | Theorems.Thm_FairChores_cost_nonneg
-- name    : FairChores.cost_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:47:18.012817+00:00
-- url     : https://prove2.me/theorems/fb899e8d-3ca8-4330-b511-c8f7950f2a93
-- title:
--   Fair Chores: cost nonneg
-- statement:
--   Every part of a feasible outcome has non-negative cost.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresModel.lean#L159-L161
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresModel.lean#L159-L161

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T]
variable {n : ℕ}
variable {c p : T → ℝ}

theorem FairChores.cost_nonneg (hc : ∀ t, 0 ≤ c t) {o : Outcome T n} (hvalid : o.Valid p) (j : Fin n) :
    0 ≤ cost c o j := by sorry
