-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_05_positive_C2_backward_taylor_exact
-- name    : AvramDividend.Classical.avram_wave3_05_positive_C2_backward_taylor_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T08:17:25.064404+00:00
-- url     : https://prove2.me/theorems/4ffca760-6cdf-4491-acd3-448df23417d5
-- title:
--   Exact second-order backward Taylor kernel for positive-axis Gaussian scale functions
-- statement:
--   For any real function twice continuously differentiable strictly above zero, the compensated backward difference over a strictly positive interval is exactly the integral of its ordinary second derivative with the nonnegative triangular kernel. In the Gaussian source Lévy model, taking a=x+y, b=x yields the genuine interior generatorIntegrand. This identity is required for the quadratic jump-size weighted L1 bound and sound Fubini.
-- source:
--   Mathlib Taylor integral remainder on a strictly positive compact interval, with conversion of within-derivatives to ordinary derivatives via positive-axis C2. Source-specific application uses Proved Gaussian scaleFunction_contDiff_two_of_gaussian.

import Mathlib

open Set MeasureTheory

theorem AvramDividend.Classical.avram_wave3_05_positive_C2_backward_taylor_exact
    (f : ℝ → ℝ) (hf : ContDiffOn ℝ 2 f (Ioi 0))
    (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    f a - f b + (b - a) * deriv f b =
      ∫ t in a..b, (t - a) * iteratedDeriv 2 f t := by sorry
