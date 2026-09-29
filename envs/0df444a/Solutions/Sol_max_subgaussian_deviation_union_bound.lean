-- Prove2me | solution 1 for max_subgaussian_deviation_union_bound
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-21T23:24:23.523189+00:00
-- url     : https://prove2.me/submissions/57b15757-7c08-4fc3-ae61-ebd2e2efc55b

import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Measure.Real

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ι : Type*} {X : ι → Ω → ℝ} {c : ι → ℝ≥0} {s : Finset ι}
    (h_subG : ∀ i ∈ s, HasSubgaussianMGF (X i) (c i) μ) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ∃ i ∈ s, ε ≤ |X i ω|}
      ≤ ∑ i ∈ s, 2 * Real.exp (-ε ^ 2 / (2 * c i)) := by
  -- single-variable two-sided sub-Gaussian tail, inlined
  have abs_ge_le : ∀ (Y : Ω → ℝ) (d : ℝ≥0), HasSubgaussianMGF Y d μ →
      μ.real {ω | ε ≤ |Y ω|} ≤ 2 * Real.exp (-ε ^ 2 / (2 * d)) := by
    intro Y d h
    have hR := h.measure_ge_le hε
    have hL := h.neg.measure_ge_le hε
    have hLset : {ω | ε ≤ (-Y) ω} = {ω | ε ≤ -(Y ω)} := by rfl
    rw [hLset] at hL
    have hsub : {ω | ε ≤ |Y ω|} ⊆ {ω | ε ≤ Y ω} ∪ {ω | ε ≤ -(Y ω)} := by
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      rcases abs_cases (Y ω) with ⟨h1, _⟩ | ⟨h1, _⟩
      · left; rw [h1] at hω; exact hω
      · right; rw [h1] at hω; exact hω
    calc μ.real {ω | ε ≤ |Y ω|}
        ≤ μ.real ({ω | ε ≤ Y ω} ∪ {ω | ε ≤ -(Y ω)}) := measureReal_mono hsub
      _ ≤ μ.real {ω | ε ≤ Y ω} + μ.real {ω | ε ≤ -(Y ω)} := measureReal_union_le _ _
      _ ≤ Real.exp (-ε ^ 2 / (2 * d)) + Real.exp (-ε ^ 2 / (2 * d)) := add_le_add hR hL
      _ = 2 * Real.exp (-ε ^ 2 / (2 * d)) := by ring
  have hev : {ω | ∃ i ∈ s, ε ≤ |X i ω|}
      = ⋃ i ∈ s, {ω | ε ≤ |X i ω|} := by
    ext ω; simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
  rw [hev]
  calc μ.real (⋃ i ∈ s, {ω | ε ≤ |X i ω|})
      ≤ ∑ i ∈ s, μ.real {ω | ε ≤ |X i ω|} := measureReal_biUnion_finset_le s _
    _ ≤ ∑ i ∈ s, 2 * Real.exp (-ε ^ 2 / (2 * c i)) := by
        apply Finset.sum_le_sum
        intro i hi
        exact abs_ge_le (X i) (c i) (h_subG i hi)
