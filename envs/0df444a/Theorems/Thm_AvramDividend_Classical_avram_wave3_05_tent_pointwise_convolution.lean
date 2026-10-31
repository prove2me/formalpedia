-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_05_tent_pointwise_convolution
-- name    : AvramDividend.Classical.avram_wave3_05_tent_pointwise_convolution
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:48:15.242015+00:00
-- url     : https://prove2.me/theorems/04af9ea8-21e1-4128-a793-c2ad0c9f8405
-- title:
--   Exact pointwise identification of the Taylor tent kernel with a real convolution
-- statement:
--   For any real-valued integrand F, real state x and nonnegative r, the exact Lebesgue convolution of the compact triangular kernel supported on (0,r] with F equals the oriented integral from zero to r of (r−t)F(x−t). The equality holds without assuming global integrability of F and is the algebraic interface required by the genuine source Gaussian Lévy generator.
-- source:
--   Pinned Mathlib and exact remote source probe b1a7d012-a24f-4324-b3de-a86d791b57db on 30 October 2026.

import Mathlib

open MeasureTheory Set intervalIntegral

theorem AvramDividend.Classical.avram_wave3_05_tent_pointwise_convolution
    (F : ℝ → ℝ) (x r : ℝ) (hr : 0 ≤ r) :
    MeasureTheory.convolution
      ((Ioc (0 : ℝ) r).indicator (fun t => r - t)) F
      (ContinuousLinearMap.mul ℝ ℝ) volume x =
        ∫ t in (0 : ℝ)..r, (r - t) * F (x - t) := by sorry
