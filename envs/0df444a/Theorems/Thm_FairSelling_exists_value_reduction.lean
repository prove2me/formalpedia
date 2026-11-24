-- Prove2me | Theorems.Thm_FairSelling_exists_value_reduction
-- name    : FairSelling.exists_value_reduction
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:09:56.167837+00:00
-- url     : https://prove2.me/theorems/b14229ff-71e2-4182-9207-d89318c896d8
-- title:
--   Fair Selling: exists value reduction
-- statement:
--   **Lowering a valuation on a set to a prescribed total.**  If the target `T` lies between the
--   total price of `A` and its total `v̄`-value, then `v` can be lowered — only on `A`, and staying
--   non-negative — so that the `v̄`-value of `A` becomes exactly `T`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EquiMMS.lean#L84-L132
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EquiMMS.lean#L84-L132

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
omit [Fintype G]

theorem FairSelling.exists_value_reduction (p : G → ℝ) (hp : ∀ g, 0 ≤ p g) (v : G → ℝ) (hv : ∀ g, 0 ≤ v g) :
    ∀ (A : Finset G) (T : ℝ), (∑ g ∈ A, p g) ≤ T → T ≤ ∑ g ∈ A, max (p g) (v g) →
    ∃ w : G → ℝ, (∀ g, 0 ≤ w g) ∧ (∀ g, w g ≤ v g) ∧ (∀ g ∉ A, w g = v g) ∧
      ∑ g ∈ A, max (p g) (w g) = T := by sorry
