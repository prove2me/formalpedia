-- Prove2me | Theorems.Thm_FairSelling_restricted_MMS2_ge_of_slack
-- name    : FairSelling.restricted_MMS2_ge_of_slack
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:36:43.191212+00:00
-- url     : https://prove2.me/theorems/50e34022-48f5-4799-b3a8-17bf7eee13f0
-- title:
--   Fair Selling: restricted MMS2 ge of slack
-- statement:
--   **General two-agent bound.**  If the goods `R` have total `v̄`-value at least `2τ` and every
--   single good has `v̄`-value at most the slack `v̄(R) - 2τ`, then the goods `R` can be split into two
--   bundles each of `v̄`-value at least `τ`, so the restricted two-agent maximin share is at least
--   `τ`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgents.lean#L367-L383
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgents.lean#L367-L383

import Mathlib
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TwoAgents
import Definitions.Def_RequestProject_MMSPartition
import Definitions.Def_RequestProject_ThreeAgents
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]

theorem FairSelling.restricted_MMS2_ge_of_slack (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g)
    (R : Finset G) (τ : ℝ) (hτ : 0 ≤ τ) (hR2 : 2 * τ ≤ vbarSum w p R)
    (hslack : ∀ g ∈ R, vbar w p g ≤ vbarSum w p R - 2 * τ) :
    τ ≤ MMS 2 (restrictVal R w) (restrictVal R p) := by sorry
