-- Prove2me | Theorems.Thm_AvramDividend_Classical_renewal_scale_finite_difference_limits_of_hasDerivAt
-- name    : AvramDividend.Classical.renewal_scale_finite_difference_limits_of_hasDerivAt
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-18T21:04:56.67804+00:00
-- url     : https://prove2.me/theorems/ab77ec0b-a6b7-42e3-aaa3-14f0c49b5420
-- title:
--   One-sided scale-function difference limits for the reflected-regulator renewal squeeze
-- statement:
--   For any real function W differentiable at the barrier a with derivative d not equal to zero, both the backward quotient h W(a-h)/(W(a)-W(a-h)) and forward quotient h W(a+h)/(W(a+h)-W(a)), mapped to extended nonnegative reals using ENNReal.ofReal, converge as h tends to zero from above to ENNReal.ofReal(W(a)/d). This is the deterministic calculus component of the two-sided renewal bounds for the killed reflected-supremum value in Avram–Palmowski–Pistorius (2007), Proposition 1. No stochastic identity is asserted here.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 1 and equation (3.13), arXiv:math/0702893; deterministic derivative-limit deduction for the level-renewal finite-difference method.

import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Instances.ENNReal.Lemmas

open Filter Topology
open scoped ENNReal

theorem AvramDividend.Classical.renewal_scale_finite_difference_limits_of_hasDerivAt
    (W : ℝ → ℝ) (a d : ℝ)
    (hD : HasDerivAt W d a) (hd : d ≠ 0) :
    Tendsto
      (fun ε : ℝ => ENNReal.ofReal
        (ε * W (a - ε) / (W a - W (a - ε))))
      (𝓝[>] (0 : ℝ)) (𝓝 (ENNReal.ofReal (W a / d))) ∧
    Tendsto
      (fun ε : ℝ => ENNReal.ofReal
        (ε * W (a + ε) / (W (a + ε) - W a)))
      (𝓝[>] (0 : ℝ)) (𝓝 (ENNReal.ofReal (W a / d))) := by sorry
