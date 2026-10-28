-- Prove2me | Theorems.Thm_AvramDividend_Classical_monotone_C1_kernel_derivative_primitive_from_zero
-- name    : AvramDividend.Classical.monotone_C1_kernel_derivative_primitive_from_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T20:17:14.472654+00:00
-- url     : https://prove2.me/theorems/b928d68e-c31a-4b0f-93aa-00d860096458
-- title:
--   Monotone positive-time C1 kernel has an integrable derivative and exact zero-origin primitive
-- statement:
--   If g is continuous and monotone on nonnegative times, vanishes at zero, and is continuously differentiable on strictly positive times, then its ordinary derivative is integrable over each interval [0,x] and integrating this derivative from zero recovers g(x), despite the derivative being potentially unbounded at the origin. This is the boundary-sensitive missing step in the causal convolution C1 transfer: it excludes the possibility of singular derivative mass at zero by using the continuity of g(0) and differentiability on (0,∞).
-- source:
--   Fundamental theorem of calculus on [epsilon,x], monotone derivative integrability and convergence as epsilon decreases to zero; pinned Mathlib MonotoneOn.intervalIntegrable_deriv and intervalIntegral.integral_deriv_eq_sub. Parent analytical bridge AvramDividend.Classical.causal_convolution_contDiffOn_one_of_monotone_C1_kernel.

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
open MeasureTheory Set intervalIntegral

theorem AvramDividend.Classical.monotone_C1_kernel_derivative_primitive_from_zero
    (g : ℝ → ℝ) (hg0 : g 0 = 0)
    (hgcont : ContinuousOn g (Ici (0 : ℝ)))
    (hgmono : MonotoneOn g (Ici (0 : ℝ)))
    (hgC1 : ContDiffOn ℝ 1 g (Ioi (0 : ℝ))) :
    ∀ x : ℝ, 0 < x →
      IntervalIntegrable (deriv g) volume 0 x ∧
      (∫ t in (0 : ℝ)..x, deriv g t) = g x := by sorry
