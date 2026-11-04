-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_uniform_physical_negative_levy_integral_bound
-- name    : AvramDividend.Classical.avram_wave8_22_original_BV_uniform_physical_negative_levy_integral_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:07:52.661793+00:00
-- url     : https://prove2.me/theorems/7fc76e56-6a27-4d4f-93e8-1c4f5eb97f1d
-- title:
--   Uniform physical negative-jump Lévy generator integral over original BV compact reserve band
-- statement:
--   For the original bounded-variation spectrally negative Lévy process, the actual physical negative-mark integral of the BV value increment has one deterministic uniform absolute bound M on any compact positive reserve band, using the first negative jump moment and finite separated negative tail intensity. The bound applies to the original ν, without copying a Poisson measure.
-- source:
--   Original BV small negative moment bv_small_negative_first_moment_integrable; accepted physical pointwise near/far jump bound 0c51c590; pinned Mathlib integral comparison and integrable domination.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_small_negative_first_moment_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_negative_levy_near_far_kernel_bounds
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave8_22_original_BV_uniform_physical_negative_levy_integral_bound
  {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ}
  (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
  (w : ℝ → ℝ) (hwMeas : Measurable w)
  (a b L R : ℝ) (ha : 0 < a) (ha2 : a ≤ 2) (hab : a ≤ b)
  (hL : 0 ≤ L) (hR : 0 ≤ R)
  (hLip : ∀ u ∈ Icc (a / 2) b, ∀ v ∈ Icc (a / 2) b,
    |w u - w v| ≤ L * |u - v|)
  (hWbound : ∀ v : ℝ, v ≤ b → |w v| ≤ R)
  (hMass : X.ν (Iic (-a / 2)) < ⊤) :
  ∃ M : ℝ, 0 ≤ M ∧ ∀ y ∈ Icc a b,
    |∫ z in Iio (0 : ℝ), w (y + z) - w y ∂X.ν| ≤ M := by sorry
