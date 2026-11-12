-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gb62_sampled_original_rightCont_filtration
-- name    : AvramDividend.Classical.avram_gb62_sampled_original_rightCont_filtration
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T12:08:40.903482+00:00
-- url     : https://prove2.me/theorems/7b6b25e2-9d7b-443b-9d82-06e840c16dc3
-- title:
--   Sampling an original right-continuous filtration on a deterministic nonnegative time grid
-- statement:
--   For any right-continuous filtration indexed by nonnegative real time and nonnegative mesh width, restriction to natural-number mesh instants gives a genuine discrete-time filtration equal pointwise to the original sigma algebras. This is a structural change of time index on the same measurable space.

import Mathlib
open MeasureTheory
open scoped NNReal

theorem AvramDividend.Classical.avram_gb62_sampled_original_rightCont_filtration
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ) (Δ : ℝ≥0) :
    ∃ (𝓖 : Filtration ℕ mΩ),
      ∀ i : ℕ, 𝓖 i = 𝓕.rightCont ((i : ℝ≥0) * Δ) := by sorry
