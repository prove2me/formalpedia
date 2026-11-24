-- Prove2me | Theorems.Thm_FairSelling_exists_canonical_of_few_large
-- name    : FairSelling.exists_canonical_of_few_large
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T03:13:20.917228+00:00
-- url     : https://prove2.me/theorems/5753fd71-cad4-49a2-a0ad-807281c36419
-- title:
--   Fair Selling: exists canonical of few large
-- statement:
--   **Proposition 6**, the case with no excess large goods (`t = 0`): if there are no more large
--   goods than parts and the value at our disposal is at least `(k−1)μ + ρμ`, a canonical partition
--   into `k` parts exists.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsProp6.lean#L1025-L1037
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsProp6.lean#L1025-L1037

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_TwoThirdsCanonical
import Definitions.Def_RequestProject_TwoThirdsBagFilling
import Definitions.Def_RequestProject_TwoThirdsProp6
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G]

theorem FairSelling.exists_canonical_of_few_large (w p : G → ℝ) (hp : ∀ g, 0 ≤ p g) {μ : ℝ} (hμ : 0 ≤ μ)
    {k : ℕ} [NeZero k] {R : Finset G} {D : ℝ} (hD : 0 ≤ D) {A C S : Finset G}
    (hRdef : R = A ∪ C ∪ S)
    (hAC : Disjoint A C) (hAS : Disjoint A S) (hCS : Disjoint C S)
    (hA1 : ∀ g ∈ A, μ / 3 ≤ vbar w p g) (hsmall : ∀ g ∈ R, vbar w p g ≤ 2 * μ / 3)
    (hC1 : ∀ g ∈ C, vbar w p g ≤ μ / 3)
    (hS1 : ∀ g ∈ S, μ / 3 ≤ p g) (hS2 : ∀ g ∈ S, w g ≤ p g)
    (hcard : A.card ≤ k)
    (hbud : ((k : ℝ) - 1) * μ + 2 * μ / 3
      ≤ (∑ g ∈ A, vbar w p g) + (∑ g ∈ C, vbar w p g) + D + ∑ g ∈ S, p g) :
    Nonempty (Canonical w p μ (2 * μ / 3) k R D) := by sorry
