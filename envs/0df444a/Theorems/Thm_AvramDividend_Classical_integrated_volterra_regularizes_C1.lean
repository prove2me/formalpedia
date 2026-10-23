-- Prove2me | Theorems.Thm_AvramDividend_Classical_integrated_volterra_regularizes_C1
-- name    : AvramDividend.Classical.integrated_volterra_regularizes_C1
-- status  : Open
-- author  : @WillR
-- created : 2026-10-22T10:49:01.8239+00:00
-- url     : https://prove2.me/theorems/1d2a9fd6-58b3-40fb-bd99-9163de2a72a8
-- title:
--   C1 smoothing for a positive-coefficient second-kind integrated Volterra equation
-- statement:
--   Suppose a>0, K is Lebesgue integrable on positive times, V is continuous and bounded on bounded positive intervals, and aV(x)+∫_0^x[β+K(x-s)]V(s)ds=x for every x>0. Then V is continuously differentiable on the positive half-line. Establish this via a causal Volterra resolvent: for sufficiently short horizons, the L1 kernel has integral norm smaller than a, so the Neumann series yields the unique continuous solution and its derivative by convolution with the constant derivative of x. Extend interval by interval. No differentiability of K or moment condition is assumed.
-- source:
--   Classical Volterra integral equations of the second kind, local L1 causal convolution Neumann contraction, fundamental theorem of calculus and uniqueness.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.integrated_volterra_regularizes_C1
    (V K : ℝ → ℝ) (a β : ℝ)
    (ha : 0 < a)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hVcont : ContinuousOn V (Ioi (0 : ℝ)))
    (hVbound : ∀ R : ℝ, 0 < R →
      ∃ C : ℝ, ∀ x : ℝ, x ∈ Ioc (0 : ℝ) R → |V x| ≤ C)
    (hEq : ∀ x : ℝ, 0 < x →
      a * V x +
        (∫ s in Ioc (0 : ℝ) x,
          (β + K (x - s)) * V s ∂volume) = x) :
    ContDiffOn ℝ 1 V (Ioi (0 : ℝ)) := by sorry
