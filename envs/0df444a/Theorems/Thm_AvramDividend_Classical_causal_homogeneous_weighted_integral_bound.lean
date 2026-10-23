-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_homogeneous_weighted_integral_bound
-- name    : AvramDividend.Classical.causal_homogeneous_weighted_integral_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T22:50:44.774987+00:00
-- url     : https://prove2.me/theorems/9305bcac-b21f-4ddc-8b0e-e512d05321b8
-- title:
--   Weighted magnitude of a homogeneous Volterra solution is bounded by positive convolution
-- statement:
--   For a>0 and a locally bounded, positive-time continuous solution D of the homogeneous causal Volterra equation, its exponentially weighted absolute value satisfies a e^(−wx)|D(x)| ≤ ∫₀ˣ e^(−w(x−s))|β+K(x−s)| · e^(−ws)|D(s)| ds. Prove using Bochner integral norm inequality and exponential additivity. This is the pointwise estimate needed by the weighted-supremum uniqueness theorem.

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Theorems.Thm_AvramDividend_Classical_causal_full_kernel_locally_bounded_input_integrable
open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_homogeneous_weighted_integral_bound
    (K D : ℝ → ℝ) (a β w : ℝ)
    (ha : 0 < a)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hDc : ContinuousOn D (Ioi (0 : ℝ)))
    (hDb : ∀ R : ℝ, 0 < R →
      ∃ C : ℝ, ∀ s : ℝ, s ∈ Ioc (0 : ℝ) R → |D s| ≤ C)
    (hEq : ∀ x : ℝ, 0 < x →
      a * D x + (∫ s in Ioc (0 : ℝ) x,
        (β + K (x - s)) * D s ∂volume) = 0)
    (x : ℝ) (hx : 0 < x) :
    a * (Real.exp (-(w * x)) * |D x|) ≤
      (∫ s in Ioc (0 : ℝ) x,
        (Real.exp (-(w * (x - s))) * |β + K (x - s)|) *
        (Real.exp (-(w * s)) * |D s|) ∂volume) := by sorry
