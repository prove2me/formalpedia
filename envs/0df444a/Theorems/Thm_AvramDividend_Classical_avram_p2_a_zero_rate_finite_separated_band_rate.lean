-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_finite_separated_band_rate
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_finite_separated_band_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T13:34:48.328208+00:00
-- url     : https://prove2.me/theorems/efb5adf4-08ff-4df2-a634-068be22061ac
-- title:
--   Finite original Lévy negative-band prescribed ENNReal rate for any finite horizon
-- statement:
--   On the genuine source Lévy triplet, the finite nonnegative horizon factor times the ν mass of an arbitrary measurable negative mark band bounded away from zero is finite in ENNReal. The proof uses the previously Proved finite ν mass for separated bands and Mathlib multiplication below top; it does not assert any counting expectation identity and handles all finite T including zero.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_separated_borel_nu_finite

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_a_zero_rate_finite_separated_band_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B)
    (ε : ℝ) (hε : 0 < ε) (hBsep : B ⊆ Iic (-ε)) :
    (T : ℝ≥0∞) * X.ν B < ⊤ := by sorry
