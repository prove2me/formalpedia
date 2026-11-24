-- Prove2me | Theorems.Thm_FairSelling_eventCost_sold_free
-- name    : FairSelling.eventCost_sold_free
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:11:46.457345+00:00
-- url     : https://prove2.me/theorems/aa48a7f8-cfd2-4064-9b7f-c2dc0ed14909
-- title:
--   Fair Selling: event Cost sold free
-- statement:
--   If the good that an event sells belongs to no part and is not one the agent intended to sell,
--   then that good only *lowers* the cost of the event, by its price.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsBudget.lean#L260-L275
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsBudget.lean#L260-L275

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

theorem FairSelling.eventCost_sold_free (E : EquiMMS w p μ k) (hp : ∀ g, 0 ≤ p g) (A : Finset G) (f : G)
    (hfp : ∀ j, f ∉ E.part j) (hfs : f ∉ E.sell) (c : ℝ) :
    eventCost E A {f} c ≤ vbarSum w p A - p f + c := by sorry
