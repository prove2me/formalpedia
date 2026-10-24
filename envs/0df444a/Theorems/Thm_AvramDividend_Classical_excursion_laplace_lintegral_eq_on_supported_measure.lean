-- Prove2me | Theorems.Thm_AvramDividend_Classical_excursion_laplace_lintegral_eq_on_supported_measure
-- name    : AvramDividend.Classical.excursion_laplace_lintegral_eq_on_supported_measure
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T20:50:46.905641+00:00
-- url     : https://prove2.me/theorems/b36c4a8b-ca7d-4ecf-9b03-4ab4c8ecd3eb
-- title:
--   Laplace integral agrees with bounded test under nonnegative support
-- statement:
--   For any real s and any measure supported on [0,∞), its ordinary exponential Laplace integral equals the bounded full-line test exp(-s max(x,0)). The identity converts weak convergence of capped Laplace integrals into the specified transform for the finite-measure Prokhorov limit.
-- source:
--   Direct measure-theoretic helper for AvramDividend.Classical.excursion_laplace_weak_limit_of_tight_approximants; Mathlib MeasureTheory OuterMeasure.AE and Integral.Lebesgue.Basic.

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.OuterMeasure.AE

open MeasureTheory Set

theorem AvramDividend.Classical.excursion_laplace_lintegral_eq_on_supported_measure
    (μ : Measure ℝ) (s : ℝ)
    (hsupport : μ (Iio (0 : ℝ)) = 0) :
    (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-(s * max x 0))) ∂μ) =
      (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-(s * x))) ∂μ) := by sorry
