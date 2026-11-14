-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb23_original_zero_contact_discounted_mark_kernel_integral_exact
-- name    : AvramDividend.Classical.avram_bvb23_original_zero_contact_discounted_mark_kernel_integral_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T07:40:14.192894+00:00
-- url     : https://prove2.me/theorems/874df19a-9881-4c4d-af9c-6971f275b94b
-- title:
--   Original finite-activity zero-reserve negative-mark generator kernel integrated against the full physical discounted Lebesgue clock
-- statement:
--   For the original spectrally negative Levy process with finite negative-mark intensity and original candidate vanishing on negative reserves, the actual negative-mark zero-reserve generator kernel integrated on the physical real-time discounted horizon equals minus the original intensity times the boundary value times the entire physical discounted clock occupation. It retains the exact source negative-mark compensator and is an intermediate bridge from the Proved zero-reserve kernel to the K time/mark integral in the original BV zero-jump survival case.
-- source:
--   Proved exact original negative-mark contact kernel 14335b0d; pinned MeasureTheory.integral_mul_const; Avram-Palmowski-Pistorius (2007) (5.13).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bvb22_original_zero_contact_negative_mark_kernel_exact
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bvb23_original_zero_contact_discounted_mark_kernel_integral_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (hw_neg : ∀ z < 0, w z = 0)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (q T : ℝ) :
    (∫ t in Ioc (0 : ℝ) T,
      Real.exp (-(q * t)) *
        (∫ z in Iio (0 : ℝ), w ((0 : ℝ) + z) - w 0 ∂X.ν)
      ∂(volume : Measure ℝ)) =
    (-(w 0) * (X.ν (Iio (0 : ℝ))).toReal) *
      (∫ t in Ioc (0 : ℝ) T,
        Real.exp (-(q * t)) ∂(volume : Measure ℝ)) := by sorry
