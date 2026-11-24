-- Prove2me | Theorems.Thm_FairSelling_exists_canonical_of_large_pairs
-- name    : FairSelling.exists_canonical_of_large_pairs
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:46:55.063953+00:00
-- url     : https://prove2.me/theorems/ac7fc108-9da6-497a-af45-932bb5afb5ac
-- title:
--   Fair Selling: exists canonical of large pairs
-- statement:
--   **Proposition 6.**  If the available resources split into large goods `A` (worth between
--   `μ/3 = (1−ρ)μ` and `2μ/3 = ρμ`), cheap goods `C` (worth at most `μ/3`) and goods `S` that the
--   agent intends to sell (of price at least `μ/3`), if there are no more large goods than parts, and
--   if the value at our disposal is at least `(k−1)μ + ρμ`, then a canonical partition into `k` parts
--   exists.
--
--   The bound `(k−1)μ + ρμ` is the manuscript's "total value at our disposal is at least
--   `(n′+1−2ρ)MMSᵢ`" after the unification of the two cases `|L′| ≤ n′` and `|L′| = n′+1`: each of the
--   `k−1` ordinary parts costs at most `μ`, and the special part needs `ρμ`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsProp6.lean#L878-L1020
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsProp6.lean#L878-L1020

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

theorem FairSelling.exists_canonical_of_large_pairs (w p : G → ℝ) (hp : ∀ g, 0 ≤ p g) {μ : ℝ} (hμ : 0 ≤ μ)
    {k : ℕ} [NeZero k] {R : Finset G} {D : ℝ} (hD : 0 ≤ D) {A C S : Finset G}
    (hRdef : R = A ∪ C ∪ S)
    (hAC : Disjoint A C) (hAS : Disjoint A S) (hCS : Disjoint C S)
    (hA1 : ∀ g ∈ A, μ / 3 ≤ vbar w p g) (hsmall : ∀ g ∈ R, vbar w p g ≤ 2 * μ / 3)
    (hC1 : ∀ g ∈ C, vbar w p g ≤ μ / 3)
    (hS1 : ∀ g ∈ S, μ / 3 ≤ p g) (hS2 : ∀ g ∈ S, w g ≤ p g)
    {t : ℕ} (hcard : A.card ≤ k + t)
    (hbud : ((k : ℝ) - 1) * μ + 2 * μ / 3 + (t : ℝ) * (μ / 3)
      ≤ (∑ g ∈ A, vbar w p g) + (∑ g ∈ C, vbar w p g) + D + ∑ g ∈ S, p g) :
    Nonempty (Canonical w p μ (2 * μ / 3) k R D) := by sorry
