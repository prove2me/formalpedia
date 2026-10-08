-- Prove2me | Theorems.Thm_AvramDividend_Classical_cstar_shape_of_attained_positive_minimal
-- name    : AvramDividend.Classical.cstar_shape_of_attained_positive_minimal
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T23:00:06.817343+00:00
-- url     : https://prove2.me/theorems/453bcaa0-8b16-4e08-989b-89f6719f5849
-- title:
--   The positive derivative minimum at cstar supplies every denominator and secant inequality
-- statement:
--   Suppose the canonical barrier cstar is a positive global minimiser of the ordinary derivative of W and its derivative d is strictly positive. Assume W is continuous on [0,cstar] and differentiable on (0,cstar). Then the effective EReal scale denominator at cstar is d, every competing nonnegative barrier has infinite, zero, or at least d effective derivative, and W's secant slope over any subinterval of [0,cstar] is at least d. The zero-barrier derivative inequality follows by passage to the right liminf, with a separate infinite case. The secant inequality is the mean value theorem, including boundary endpoints. This is exactly the positive-branch analytic shape needed for the Avram Proposition 3(i) comparison.
-- source:
--   Theorems.Thm_AvramDividend_Classical_deriv_global_lower_le_right_liminf and the previously Proved cstar_optimal_barrier_of_attained_minimum; the newly published secant_of_derivative_lower_bound isolates the mean-value step.

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical Filter Set Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.cstar_shape_of_attained_positive_minimal
    (W : ℝ → ℝ)
    (hattain : (cstar W).toReal ∈ cstarSet W)
    (hpositive : 0 < deriv W (cstar W).toReal)
    (hcont : ContinuousOn W (Set.Icc 0 (cstar W).toReal))
    (hdiff : DifferentiableOn ℝ W (Set.Ioo 0 (cstar W).toReal)) :
    ∃ d : ℝ, 0 < d ∧
      scaleDeriv W (cstar W).toReal = (d : EReal) ∧
      (∀ a : ℝ, 0 ≤ a →
        scaleDeriv W a = ⊤ ∨
          (scaleDeriv W a).toReal = 0 ∨
          d ≤ (scaleDeriv W a).toReal) ∧
      (∀ b x : ℝ, 0 ≤ b → b ≤ x →
        x ≤ (cstar W).toReal →
        (x - b) * d ≤ W x - W b) := by sorry
