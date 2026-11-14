-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb36_source_physical_discount_Ioc_lintegral_eq_ofReal_real_integral
-- name    : AvramDividend.Classical.avram_bvb36_source_physical_discount_Ioc_lintegral_eq_ofReal_real_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T11:31:47.505991+00:00
-- url     : https://prove2.me/theorems/f437382b-7c18-4552-9157-e27d827fc7e2
-- title:
--   Exact original finite physical-horizon discounted ENNReal Lebesgue mass equals finite real Ioc integral
-- statement:
--   For the exact source physical discounted exponential exp(-q*t) on the real positive-time interval Ioc(0,T), the full extended-nonnegative Lebesgue lintegral equals ENNReal.ofReal of the ordinary finite real Bochner integral on the same original interval. Continuity on compact physical-time intervals supplies integrability and the exponential is strictly positive. This provides the precise clock conversion for the surviving source full-horizon compensated negative-mark Stieltjes cash ceiling, with no artificial discount or measure.
-- source:
--   Pinned Mathlib ofReal_integral_eq_lintegral_ofReal and Continuous.integrableOn_Ioc; source Ioc physical clock of 09a9c1c4 and 1569d325.

import Mathlib
open Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb36_source_physical_discount_Ioc_lintegral_eq_ofReal_real_integral
    (q T : ℝ) :
    (∫⁻ t in Ioc (0 : ℝ) T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(volume : Measure ℝ)) =
    ENNReal.ofReal (∫ t in Ioc (0 : ℝ) T,
      Real.exp (-(q * t)) ∂(volume : Measure ℝ)) := by sorry
