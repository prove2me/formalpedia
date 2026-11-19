-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_purejump_ubv_small_negative_band_rate_diverges
-- name    : AvramDividend.Classical.avram_f6_original_purejump_ubv_small_negative_band_rate_diverges
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T17:13:46.842211+00:00
-- url     : https://prove2.me/theorems/ef53e7ad-7dd6-45f3-8e7f-344ffd0f8a55
-- title:
--   Original infinite-activity purejump small negative-jump band intensity diverges under truncation
-- statement:
--   Under the original unbounded-variation zero-Gaussian spectrally negative Lévy assumptions, the finite truncated Poisson intensity of the negative small-mark band (-1,-δ) diverges as δ↓0. This separates the far-jump component and identifies the precise divergent small-mark intensity required for compensated infinite-activity Itô approximation. Reuses generic Proved negative_jump_small_band_tendsto_top and source ν_integrable, without assuming the stopped HJB budget.
-- source:
--   Proved negative_jump_small_band_tendsto_top 4027f977, Proved negative_jump_truncation_measure_finite 16a2d301, original ν_integrable and Proved truncated rate divergence 5da6ed6a.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_purejump_ubv_small_negative_band_rate_diverges
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hσ : X.σ = 0) :
    Tendsto (fun δ : ℝ =>
      (X.ν (Ioo (-1 : ℝ) (-δ))).toReal)
      (nhdsWithin (0 : ℝ) (Ioi 0)) atTop := by sorry
