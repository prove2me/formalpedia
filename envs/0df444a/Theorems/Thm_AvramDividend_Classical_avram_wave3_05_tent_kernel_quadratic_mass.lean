-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_05_tent_kernel_quadratic_mass
-- name    : AvramDividend.Classical.avram_wave3_05_tent_kernel_quadratic_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:35:13.389277+00:00
-- url     : https://prove2.me/theorems/350c6078-b3ad-4048-98a8-14de9527ee3d
-- title:
--   Exact quadratic mass of the positive triangular Taylor convolution kernel
-- statement:
--   The triangular kernel supported on the positive interval (0,r] has total Lebesgue mass r²/2 for r≥0. This exact second-order mass is the quantitative constant in the Gaussian weighted small-jump Fubini bound; it will be combined with the already Proved source generator Taylor identity and convolution integral factorisation.
-- source:
--   Pinned Mathlib interval integral of identity, difference of interval integrals, MeasureTheory.integral_indicator, and intervalIntegral.integral_of_le.

import Mathlib

open Set MeasureTheory intervalIntegral

theorem AvramDividend.Classical.avram_wave3_05_tent_kernel_quadratic_mass
    (r : ℝ) (hr : 0 ≤ r) :
    (∫ t : ℝ, (Ioc (0 : ℝ) r).indicator (fun t => r - t) t) =
      r ^ 2 / 2 := by sorry
