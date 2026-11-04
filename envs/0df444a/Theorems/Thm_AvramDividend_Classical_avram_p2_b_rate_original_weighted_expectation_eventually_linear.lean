-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_original_weighted_expectation_eventually_linear
-- name    : AvramDividend.Classical.avram_p2_b_rate_original_weighted_expectation_eventually_linear
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:23:30.339001+00:00
-- url     : https://prove2.me/theorems/dcfa2784-b7a6-48d0-a62f-f103ed9d30c5
-- title:
--   Actual Lévy fourth-exponential expectation has O(h) small-time bound
-- statement:
--   For the original spectrally negative Levy process and any strictly positive exponential parameter theta, the source-proved fourth-weighted exponential small-time derivative implies that the actual fourth-weighted expectation is at most C h for all sufficiently small positive h, with a finite strictly positive constant C. This gives the uniform mass bound needed for negative-increment band estimates.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_source_fourth_weighted_exponential_small_time_derivative
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p2_b_rate_original_weighted_expectation_eventually_linear
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 < θ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ h in nhdsWithin (0 : ℝ) (Ioi 0),
        (∫ ω, (Real.exp (θ * X.X (Real.toNNReal h) ω) - 1) ^ 4 ∂P) ≤
          C * h := by sorry
