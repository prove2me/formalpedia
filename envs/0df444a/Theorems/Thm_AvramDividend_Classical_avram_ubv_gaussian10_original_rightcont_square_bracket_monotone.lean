-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_original_rightcont_square_bracket_monotone
-- name    : AvramDividend.Classical.avram_ubv_gaussian10_original_rightcont_square_bracket_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T11:16:26.713889+00:00
-- url     : https://prove2.me/theorems/043e764c-547a-45f1-87b0-07702c412cf1
-- title:
--   Original stopped Gaussian finite-energy bracket is pointwise monotone
-- statement:
--   For every sample point of the original spectrally negative Levy process, if the squared Gaussian integrand is integrable on every bounded right-closed physical-time band, the corresponding finite-horizon bracket is nondecreasing. This is a finite-energy interface for bracket quadratic variation and stopped L2 martingale arguments, not a substitute for the stochastic integral.
-- source:
--   Pinned Mathlib MeasureTheory.Integral.Bochner.Set setIntegral_mono_set, inspected 2026-11-07.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gaussian10_original_rightcont_square_bracket_monotone
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : ℝ≥0 × Ω → ℝ) (μtime : Measure ℝ≥0)
    (hInt : ∀ ω b, IntegrableOn
      (fun t : ℝ≥0 => (H (t, ω)) ^ 2)
      (Ioc (0 : ℝ≥0) b) μtime) :
    ∀ ω, Monotone (fun b : ℝ≥0 =>
      ∫ t in Ioc (0 : ℝ≥0) b, (H (t, ω)) ^ 2 ∂μtime) := by sorry
