-- Prove2me | Theorems.Thm_FairSelling_EquiMMS_budget_univ
-- name    : FairSelling.EquiMMS.budget_univ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:09:46.576038+00:00
-- url     : https://prove2.me/theorems/f2f90fc9-8ae1-4d1c-9763-19939eca6f98
-- title:
--   Equi MMS: budget univ
-- statement:
--   Before anything has been allocated, the budget is exactly `k · μ`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EquiMMS.lean#L71-L76
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EquiMMS.lean#L71-L76

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_EquiMMS
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}

theorem FairSelling.EquiMMS.budget_univ {w p : G → ℝ} {μ : ℝ} {k : ℕ} (E : EquiMMS w p μ k) :
    E.budget Finset.univ 0 = k * μ := by sorry
