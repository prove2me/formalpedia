-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_original_levy_weighted_lintegral_finite
-- name    : AvramDividend.Classical.avram_p2_b_rate_original_levy_weighted_lintegral_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T19:51:31.292198+00:00
-- url     : https://prove2.me/theorems/91f79ee5-96fc-4b9a-afbe-b277cedf8b9a
-- title:
--   Original Lévy measure shifted fourth-exponential lower integral is finite
-- statement:
--   Every actual source Lévy measure fourth-weighted shifted exponential mark law is a finite nonnegative measure on negative jump marks. This converts the proved original source Bochner-integrability into a finite ENNReal lower integral and supplies mass tightness for the Laplace/moment inversion bridge. It assumes no jump rate and requires the independently accepted source ν weighted integrability helper.

import Mathlib
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_original_levy_weighted_moment_integrable

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_b_rate_original_levy_weighted_lintegral_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ρ θ : ℝ) (hρ : 0 ≤ ρ) (hθ : 0 ≤ θ) :
    (∫⁻ y in Iio (0 : ℝ), ENNReal.ofReal
      (Real.exp (ρ * y) * (Real.exp (θ * y) - 1) ^ 4) ∂X.ν) < ⊤ := by sorry
