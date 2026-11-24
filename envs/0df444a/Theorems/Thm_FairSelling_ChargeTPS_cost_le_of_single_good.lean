-- Prove2me | Theorems.Thm_FairSelling_ChargeTPS_cost_le_of_single_good
-- name    : FairSelling.ChargeTPS.cost_le_of_single_good
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:44:21.138367+00:00
-- url     : https://prove2.me/theorems/b8a58426-dd88-4b62-a7b9-0ce401522919
-- title:
--   Charge TPS: cost le of single good
-- statement:
--   **A package of cash drawn from one single good.**  An agent holding `q` in proceeds of the
--   single good `g`, and charged with that good's sale loss, costs at most the truncation level.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxServe.lean#L54-L57
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxServe.lean#L54-L57

import Mathlib
import Definitions.Def_RequestProject_TPSSefxCharge
import Definitions.Def_RequestProject_TPSSefxServe
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [Fintype G] [DecidableEq G]

theorem FairSelling.ChargeTPS.cost_le_of_single_good (w p : G → ℝ) (t : ℝ) (g : G) (q : ℝ) (hqp : q ≤ p g) (hqt : q ≤ t) :
    truncBundle w p t ∅ + q + 0 + ∑ x ∈ ({g} : Finset G), saleLoss w p t x ≤ t := by sorry
