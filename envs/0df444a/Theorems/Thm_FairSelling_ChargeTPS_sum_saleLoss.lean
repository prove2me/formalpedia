-- Prove2me | Theorems.Thm_FairSelling_ChargeTPS_sum_saleLoss
-- name    : FairSelling.ChargeTPS.sum_saleLoss
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:19:29.789539+00:00
-- url     : https://prove2.me/theorems/b44c6e6d-2e7a-4ee5-be02-2f5861d5a252
-- title:
--   Charge TPS: sum sale Loss
-- statement:
--   The sale loss of a set of goods is its truncated value minus its price.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxCharge.lean#L84-L87
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxCharge.lean#L84-L87

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaEleven
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSSefxGeneral
import Definitions.Def_RequestProject_TPSSefxCharge
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [Fintype G] [DecidableEq G]

theorem FairSelling.ChargeTPS.sum_saleLoss (w p : G → ℝ) (t : ℝ) (X : Finset G) :
    ∑ g ∈ X, saleLoss w p t g = truncBundle w p t X - ∑ g ∈ X, p g := by sorry
