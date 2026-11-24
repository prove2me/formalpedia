-- Prove2me | Theorems.Thm_FairSelling_eventCost_witness
-- name    : FairSelling.eventCost_witness
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:11:49.097551+00:00
-- url     : https://prove2.me/theorems/336d88d2-2277-4fff-93f3-e79accf53748
-- title:
--   Fair Selling: event Cost witness
-- statement:
--   **Every loss event is either cheap or charged to a good of a part.**  This refines
--   `eventCost_le`: an event either costs at most the threshold `t = (2/3)·μ`, or it can be charged
--   to one of the goods it takes away that belongs to a part of the equi-valued partition, at a cost
--   of at most that good's `v̄`-value plus `μ/3`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsBudget.lean#L282-L362
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsBudget.lean#L282-L362

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

theorem FairSelling.eventCost_witness (E : EquiMMS w p μ k) (hp : ∀ g, 0 ≤ p g)
    (hμ : 0 ≤ μ) {t : ℝ} (ht : t = (2 / 3) * μ)
    {Ea Fa : Finset G} (hEF : Disjoint Ea Fa) {c : ℝ}
    (hloss : LossOK w p E.sell μ t Ea Fa c) :
    eventCost E Ea Fa c ≤ t ∨
      ∃ x ∈ Ea ∪ Fa, (∃ j, x ∈ E.part j) ∧ eventCost E Ea Fa c ≤ vbar w p x + μ / 3 := by sorry
