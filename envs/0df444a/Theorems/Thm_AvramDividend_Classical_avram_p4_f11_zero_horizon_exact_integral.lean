-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f11_zero_horizon_exact_integral
-- name    : AvramDividend.Classical.avram_p4_f11_zero_horizon_exact_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T18:45:58.897672+00:00
-- url     : https://prove2.me/theorems/07961620-dee4-46e9-984d-e73a7ff4b1fa
-- title:
--   Exact zero-horizon original Lévy discounted stopped-potential expectation
-- statement:
--   For every original spectrally negative Lévy process and Borel potential w, a three-way corrected first-exit time truncated at time zero is exactly zero, so the discounted expected terminal potential is the initial potential w(1), with probability normalization from X.isProbability and X.X_zero.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f11_zero_horizon_exact_integral
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (w : ℝ → ℝ) (b : ℝ) :
    let τ : Ω → ℝ≥0∞ := fun ω =>
      min (twoSidedExitUpTimeCorrected X (b - 1) ω)
        (min (twoSidedExitDownTimeCorrected X (-1) ω) (0 : ℝ≥0∞))
    (∫ ω, Real.exp (-(q * ENNReal.toReal (τ ω))) *
        w (1 + X.X (ENNReal.toNNReal (τ ω)) ω) ∂P) = w 1 := by sorry
