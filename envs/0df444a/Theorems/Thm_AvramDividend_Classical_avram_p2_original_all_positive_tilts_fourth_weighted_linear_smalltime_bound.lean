-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_original_all_positive_tilts_fourth_weighted_linear_smalltime_bound
-- name    : AvramDividend.Classical.avram_p2_original_all_positive_tilts_fourth_weighted_linear_smalltime_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T07:14:41.227243+00:00
-- url     : https://prove2.me/theorems/17d80ed6-1cc1-4a32-9be8-11fce7ce30d4
-- title:
--   Every positive exponential tilt has an O(h) original fourth-weighted moment
-- statement:
--   For the unchanged original spectrally negative Lévy process, every fixed nonnegative exponential tilt rho admits a finite positive C such that the actual source expectation of exp(rho X_h)(exp(X_h)-1)^4 is at most C h for sufficiently small positive time h. It directly follows from the already Proved original fourth-weighted small-time Lévy-measure derivative without a Poisson proxy or compensator, and supplies bounded tilted moments of the finite weighted small-time source measures needed for Prokhorov tightness and moment uniform-integrability arguments.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_source_fourth_weighted_exponential_small_time_derivative

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_original_all_positive_tilts_fourth_weighted_linear_smalltime_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
        (∫ ω, Real.exp (ρ * X.X (Real.toNNReal h) ω) *
          (Real.exp (X.X (Real.toNNReal h) ω) - 1) ^ 4 ∂P) ≤
          C * h := by sorry
