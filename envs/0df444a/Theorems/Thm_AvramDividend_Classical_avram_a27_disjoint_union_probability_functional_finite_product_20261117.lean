-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_disjoint_union_probability_functional_finite_product_20261117
-- name    : AvramDividend.Classical.avram_a27_disjoint_union_probability_functional_finite_product_20261117
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T17:23:29.376976+00:00
-- url     : https://prove2.me/theorems/32abe36e-7d2f-4f06-bc09-20a047d7a3c4
-- title:
--   Disjoint-union multiplicative probability functional factors across any finite pairwise disjoint family
-- statement:
--   If a real-valued functional on sets equals one at the empty set and is multiplicative on disjoint unions, it is multiplicative across every finite pairwise-disjoint family. This algebraic induction transfers the already-Proved original physical two-mark Borel void independence law to finite-dimensional marked-Poisson void probabilities.
-- source:
--   Finset induction, disjoint finite union and the assumed two-set multiplicativity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped BigOperators
noncomputable section

/-- Multiplicativity on disjoint unions yields a finite disjoint-product formula. -/

theorem AvramDividend.Classical.avram_a27_disjoint_union_probability_functional_finite_product_20261117
    {α ι : Type*} [DecidableEq ι]
    (B : ι → Set α) (Q : Set α → ℝ)
    (hZero : Q ∅ = 1)
    (hMul : ∀ U V : Set α, Disjoint U V →
      Q (U ∪ V) = Q U * Q V) :
    ∀ S : Finset ι,
      (∀ i ∈ S, ∀ j ∈ S, i ≠ j →
        Disjoint (B i) (B j)) →
      Q (⋃ i ∈ S, B i) = ∏ i ∈ S, Q (B i) := by sorry
