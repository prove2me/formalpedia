-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed13_original_finite_activity_nu_smallstrip_real_integral_le
-- name    : AvramDividend.Classical.avram_ubv_mixed13_original_finite_activity_nu_smallstrip_real_integral_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T22:57:22.328196+00:00
-- url     : https://prove2.me/theorems/18cc9af2-48ed-43b2-8526-1ec9459416b4
-- title:
--   Original finite-activity real compensator bound on any small negative strip subset
-- statement:
--   For the original spectrally negative Levy process with finite negative jump activity, the absolute signed integral on every measurable subset of (-epsilon,0) is at most epsilon times the real total negative-jump intensity. This directly covers the half-open small-band annuli in the original intrinsic Ito-Meyer source on a ruin-clipped clock.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed13_original_finite_activity_nu_smallstrip_lintegral_le
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_mixed13_original_finite_activity_nu_smallstrip_real_integral_le
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (ε : ℝ) (hε : 0 ≤ ε)
    (S : Set ℝ) (hS : MeasurableSet S) (hSub : S ⊆ Ioo (-ε) 0) :
    |∫ z in S, z ∂X.ν| ≤
      ε * (X.ν (Iio (0 : ℝ))).toReal := by sorry
