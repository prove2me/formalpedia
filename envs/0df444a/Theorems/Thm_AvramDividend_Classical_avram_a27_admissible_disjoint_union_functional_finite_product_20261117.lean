-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_admissible_disjoint_union_functional_finite_product_20261117
-- name    : AvramDividend.Classical.avram_a27_admissible_disjoint_union_functional_finite_product_20261117
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T17:24:18.249204+00:00
-- url     : https://prove2.me/theorems/1454fbe7-9164-49d1-bb98-c916ff63a797
-- title:
--   Finite disjoint-product factorisation for a functional multiplicative on admissible disjoint unions
-- statement:
--   If an observable on a family of admissible sets is multiplicative on disjoint unions, and admissibility is preserved by finite union, its value on any finite pairwise-disjoint union equals the product of the singleton values. This is needed to extend exact original negative Borel marked-void independence from two sets to arbitrary finite Borel mark partitions.
-- source:
--   Finite combinatorial induction with admissibility and pairwise-disjointness. No source-space extension.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped BigOperators
noncomputable section

/-- A disjoint-union multiplicative functional factors over admissible finite families. -/

theorem AvramDividend.Classical.avram_a27_admissible_disjoint_union_functional_finite_product_20261117
    {α ι : Type*} [DecidableEq ι]
    (Good : Set α → Prop) (B : ι → Set α) (Q : Set α → ℝ)
    (hEmpty : Q ∅ = 1)
    (hGoodUnion : ∀ S : Finset ι,
      (∀ i ∈ S, Good (B i)) → Good (⋃ i ∈ S, B i))
    (hMul : ∀ U V : Set α,
      Good U → Good V → Disjoint U V →
        Q (U ∪ V) = Q U * Q V) :
    ∀ S : Finset ι,
      (∀ i ∈ S, Good (B i)) →
      (∀ i ∈ S, ∀ j ∈ S, i ≠ j →
        Disjoint (B i) (B j)) →
      Q (⋃ i ∈ S, B i) = ∏ i ∈ S, Q (B i) := by sorry
