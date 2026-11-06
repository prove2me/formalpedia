-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f4_purejump_original_hjb_jump_drift_le
-- name    : AvramDividend.Classical.avram_p4_f4_purejump_original_hjb_jump_drift_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T00:07:18.181307+00:00
-- url     : https://prove2.me/theorems/74e69392-5a43-485b-b66b-7d2846c6cda1
-- title:
--   Original pure-jump source HJB sign, generator with zero Gaussian term
-- statement:
--   When the original spectrally negative Lévy process has zero Gaussian coefficient, its nonpositive discounted HJB residual is exactly deterministic drift plus Lévy jump generator integral.
-- source:
--   Canonical generator and HJB sign specialised to pure-jump σ=0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f4_purejump_original_hjb_jump_drift_le
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hσ : X.σ = 0)
    (q : ℝ) (w : ℝ → ℝ) (y : ℝ)
    (hGen : X.GeneratorIntegrable w y ∧
      X.generator w y - q * w y ≤ 0) :
    X.c * deriv w y +
      (∫ z in Iio (0 : ℝ), SpectrallyNegativeLevy.generatorIntegrand w y z ∂X.ν) -
        q * w y ≤ 0 := by sorry
