-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f4_zero_levy_original_hjb_gaussian_drift_le
-- name    : AvramDividend.Classical.avram_p4_f4_zero_levy_original_hjb_gaussian_drift_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T23:51:46.782556+00:00
-- url     : https://prove2.me/theorems/9e78bfcc-13fe-47df-a8e7-e59a776c8731
-- title:
--   Original no-jump source HJB becomes pure Gaussian drift inequality
-- statement:
--   The original HJB generator sign on a no-jump Lévy process reduces exactly to its Gaussian second derivative and deterministic drift first derivative, after discounting.
-- source:
--   HJB sign and generator formula, zero jump measure integral.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f4_zero_levy_original_hjb_gaussian_drift_le
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0)
    (q : ℝ) (w : ℝ → ℝ) (y : ℝ)
    (hGen : X.GeneratorIntegrable w y ∧
      X.generator w y - q * w y ≤ 0) :
    X.σ ^ 2 / 2 * iteratedDeriv 2 w y +
      X.c * deriv w y - q * w y ≤ 0 := by sorry
