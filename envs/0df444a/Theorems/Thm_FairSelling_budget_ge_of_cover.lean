-- Prove2me | Theorems.Thm_FairSelling_budget_ge_of_cover
-- name    : FairSelling.budget_ge_of_cover
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:46:13.714612+00:00
-- url     : https://prove2.me/theorems/519f7a90-3d27-4b35-8c4b-176e66c4f58b
-- title:
--   Fair Selling: budget ge of cover
-- statement:
--   **The budget in terms of the event costs.**  If the goods that are no longer available are
--   covered by the pairwise disjoint events, then the budget of an equi-valued partition in the state
--   `(R, D)` is at least its initial value `n·μ` minus the total cost of the events.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsBudget.lean#L371-L412
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsBudget.lean#L371-L412

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

theorem FairSelling.budget_ge_of_cover {w p : G → ℝ} {μ : ℝ} (E : EquiMMS w p μ n) (R : Finset G) (D : ℝ)
    (alloc sold : Fin n → Finset G) (paid : Fin n → ℝ)
    (hdisj2 : ∀ b b', b ≠ b' → Disjoint (alloc b ∪ sold b) (alloc b' ∪ sold b'))
    (hdisjR : ∀ b, Disjoint R (alloc b ∪ sold b))
    (hcover : (Finset.univ : Finset G) = R ∪ Finset.univ.biUnion (fun b => alloc b ∪ sold b))
    (hmoney : (∑ b, ∑ g ∈ sold b, p g) - ∑ b, paid b ≤ D) :
    (n : ℝ) * μ - ∑ b, eventCost E (alloc b) (sold b) (paid b) ≤ E.budget R D := by sorry
