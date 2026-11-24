-- Prove2me | Theorems.Thm_FairSelling_eventCost_le_aux
-- name    : FairSelling.eventCost_le_aux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:46:09.050393+00:00
-- url     : https://prove2.me/theorems/3cb2f947-41f7-4328-81d6-a504f9651e17
-- title:
--   Fair Selling: event Cost le aux
-- statement:
--   The cost of an event is bounded by the `v̄`-value of the goods it hands out, plus the money it
--   hands out, plus the amount by which the goods it sells are worth more to the agent than their
--   price.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsBudget.lean#L145-L172
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsBudget.lean#L145-L172

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

theorem FairSelling.eventCost_le_aux (E : EquiMMS w p μ k) (hp : ∀ g, 0 ≤ p g)
    (Ea Fa : Finset G) (hEF : Disjoint Ea Fa) (c : ℝ) :
    eventCost E Ea Fa c ≤ vbarSum w p Ea + (∑ g ∈ Fa, (vbar w p g - p g)) + c := by sorry
