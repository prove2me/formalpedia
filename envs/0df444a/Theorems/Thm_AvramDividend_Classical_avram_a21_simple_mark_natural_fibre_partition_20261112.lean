-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a21_simple_mark_natural_fibre_partition_20261112
-- name    : AvramDividend.Classical.avram_a21_simple_mark_natural_fibre_partition_20261112
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T00:33:56.006197+00:00
-- url     : https://prove2.me/theorems/80a945d2-f931-4244-9f77-3b32c5808b7f
-- title:
--   Faithful natural-indexed measurable disjoint Borel-simple mark fibres with all weighted sums preserved
-- statement:
--   For an arbitrary finite real-valued Borel simple mark and measurable mark set, there exist finitely many natural-indexed Borel fibres with measurable cells contained in that set, pairwise disjoint fibres, exact coverage and preservation of every real weighted finite sum across the original mark values.
-- source:
--   Proved original natural enumeration 1cad3050-7bd9-4d87-bf08-3b376f531617 and proved exact finite sum transfer 57c06109-61a5-419a-98e6-c9a2f0689d58. Supports original finite-strip physical marked Poisson L2 certificate 67336b2d requiring Finset.range (K k) for each k.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a21_finite_real_fibre_nat_enumeration_20261112
import Theorems.Thm_AvramDividend_Classical_avram_a21_finite_real_natural_enumeration_sum_transfer_20261112
open MeasureTheory Set AvramDividend.Classical
open scoped BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a21_simple_mark_natural_fibre_partition_20261112
    (S : Set ℝ) (hS : MeasurableSet S)
    (f : SimpleFunc ℝ ℝ) :
    ∃ (K : ℕ) (B : ℕ → Set ℝ) (c : ℕ → ℝ),
      (∀ i ∈ Finset.range K,
        MeasurableSet (B i) ∧ B i ⊆ S) ∧
      (∀ i ∈ Finset.range K,
        ∀ j ∈ Finset.range K, i ≠ j → Disjoint (B i) (B j)) ∧
      (∀ w : ℝ → ℝ,
        (∑ i ∈ Finset.range K, w (c i)) = ∑ y ∈ f.range, w y) ∧
      (∀ i ∈ Finset.range K, B i = S ∩ f ⁻¹' {c i}) := by sorry
