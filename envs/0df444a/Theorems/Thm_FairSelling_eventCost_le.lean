-- Prove2me | Theorems.Thm_FairSelling_eventCost_le
-- name    : FairSelling.eventCost_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:46:27.278234+00:00
-- url     : https://prove2.me/theorems/9b5c0834-d552-48ac-89d9-7b8f3d0880b0
-- title:
--   Fair Selling: event Cost le
-- statement:
--   **The cost of a loss event is at most `μ`.**  This is the manuscript's case analysis over the
--   four loss types of Definition 7, and it is where the value `ρ = 2/3` is used: for a loss of type
--   `ℓ₃` or `ℓ₄` the bound comes out as `3t − μ`, which equals `μ` exactly when `t = (2/3)·μ`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsBudget.lean#L178-L255
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsBudget.lean#L178-L255

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_EquiMMS
import Definitions.Def_RequestProject_TwoThirdsLoss
import Definitions.Def_RequestProject_TwoThirdsBudget
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
variable {w p : G → ℝ} {μ : ℝ} {k : ℕ}
omit [Fintype G]

theorem FairSelling.eventCost_le (E : EquiMMS w p μ k) (hp : ∀ g, 0 ≤ p g)
    (hμ : 0 ≤ μ) {t : ℝ} (ht : t = (2 / 3) * μ)
    {Ea Fa : Finset G} (hEF : Disjoint Ea Fa) {c : ℝ}
    (hloss : LossOK w p E.sell μ t Ea Fa c) :
    eventCost E Ea Fa c ≤ μ := by sorry
