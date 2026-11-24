-- Prove2me | Theorems.Thm_FairSelling_ChargeTPS_cost_le_of_footprint
-- name    : FairSelling.ChargeTPS.cost_le_of_footprint
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:43:52.492781+00:00
-- url     : https://prove2.me/theorems/eae0eb26-28d0-4eda-9102-f3aefaf8c751
-- title:
--   Charge TPS: cost le of footprint
-- statement:
--   **A self-financed package costs its footprint.**  If the cash `q` and the money `r` put aside
--   add up to the proceeds of the sold part `S₀`, then the package's cost to an agent is exactly the
--   truncated value of the whole footprint `S ∪ S₀`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxServe.lean#L45-L49
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxServe.lean#L45-L49

import Mathlib
import Definitions.Def_RequestProject_TPSSefxCharge
import Definitions.Def_RequestProject_TPSSefxServe
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [Fintype G]

theorem FairSelling.ChargeTPS.cost_le_of_footprint (w p : G → ℝ) (t : ℝ) (S S₀ : Finset G) (hdisj : Disjoint S S₀)
    (q r : ℝ) (hqr : q + r = ∑ g ∈ S₀, p g) :
    truncBundle w p t S + q + r + ∑ g ∈ S₀, saleLoss w p t g = truncBundle w p t (S ∪ S₀) := by sorry
