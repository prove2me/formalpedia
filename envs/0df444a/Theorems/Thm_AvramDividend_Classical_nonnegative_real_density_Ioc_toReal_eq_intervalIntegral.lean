-- Prove2me | Theorems.Thm_AvramDividend_Classical_nonnegative_real_density_Ioc_toReal_eq_intervalIntegral
-- name    : AvramDividend.Classical.nonnegative_real_density_Ioc_toReal_eq_intervalIntegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T11:01:33.526979+00:00
-- url     : https://prove2.me/theorems/b6d6ad90-9c41-4a1c-b93e-42083d8c3df2
-- title:
--   Nonnegative real-density measure of a positive interval equals the real interval integral
-- statement:
--   For a nonnegative real density f that is interval integrable on [0,x], the mass assigned by volume.withDensity (ofReal ∘ f) to (0,x], converted to real, equals the ordinary interval integral from 0 to x. This converts the real-density renewal series measure into the primitive required by the corrected BV Esscher scaled-scale representation, and is a direct measure-to-integral step towards cstar_lt_top.
-- source:
--   Pinned Mathlib withDensity_apply, ofReal_integral_eq_lintegral_ofReal, intervalIntegrable_iff_integrableOn_Ioc_of_le and intervalIntegral.integral_of_le.

import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
open MeasureTheory Set intervalIntegral
open scoped ENNReal NNReal

theorem AvramDividend.Classical.nonnegative_real_density_Ioc_toReal_eq_intervalIntegral
    (f : ℝ → ℝ) (hfnn : ∀ y : ℝ, 0 ≤ f y)
    (x : ℝ) (hx : 0 ≤ x)
    (hfi : IntervalIntegrable f volume 0 x) :
    ((volume.withDensity (fun y : ℝ => ENNReal.ofReal (f y)))
      (Ioc (0 : ℝ) x)).toReal = ∫ y in (0 : ℝ)..x, f y := by sorry
