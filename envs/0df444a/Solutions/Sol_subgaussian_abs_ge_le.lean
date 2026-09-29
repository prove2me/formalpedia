-- Prove2me | solution 1 for subgaussian_abs_ge_le
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-21T23:20:23.360777+00:00
-- url     : https://prove2.me/submissions/d004df7f-4d99-483e-8d92-8b2c4a9e1a8d

import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Measure.Real

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {c : ℝ≥0} (h : HasSubgaussianMGF X c μ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ |X ω|} ≤ 2 * Real.exp (-ε ^ 2 / (2 * c)) := by
  have hR := h.measure_ge_le hε
  have hL := h.neg.measure_ge_le hε
  have hLset : {ω | ε ≤ (-X) ω} = {ω | ε ≤ -(X ω)} := by rfl
  rw [hLset] at hL
  have hsub : {ω | ε ≤ |X ω|} ⊆ {ω | ε ≤ X ω} ∪ {ω | ε ≤ -(X ω)} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    rcases abs_cases (X ω) with ⟨h1, _⟩ | ⟨h1, _⟩
    · left; rw [h1] at hω; exact hω
    · right; rw [h1] at hω; exact hω
  calc μ.real {ω | ε ≤ |X ω|}
      ≤ μ.real ({ω | ε ≤ X ω} ∪ {ω | ε ≤ -(X ω)}) := measureReal_mono hsub
    _ ≤ μ.real {ω | ε ≤ X ω} + μ.real {ω | ε ≤ -(X ω)} := measureReal_union_le _ _
    _ ≤ Real.exp (-ε ^ 2 / (2 * c)) + Real.exp (-ε ^ 2 / (2 * c)) := add_le_add hR hL
    _ = 2 * Real.exp (-ε ^ 2 / (2 * c)) := by ring
