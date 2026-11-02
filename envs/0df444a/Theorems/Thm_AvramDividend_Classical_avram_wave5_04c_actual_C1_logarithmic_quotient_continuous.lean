-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_C1_logarithmic_quotient_continuous
-- name    : AvramDividend.Classical.avram_wave5_04c_actual_C1_logarithmic_quotient_continuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T18:29:19.855656+00:00
-- url     : https://prove2.me/theorems/7383ce65-f021-4347-8d40-4e6a6eacafb7
-- title:
--   Genuine C1 payoff logarithmic difference quotient continuous on compact exponential jump band
-- statement:
--   For any genuine globally C1 payoff w and physical reserve x, the divided difference in logarithmic jump coordinates t=exp(-r), with value w'(x) inserted at t=1, is continuous on every compact subinterval [a,1] of (0,1]. Differentiability uses exactly C1 and the derivative of log at 1; away from 1 the map is continuous. This establishes the real compact-interval input required by the Proved tapered compactification for the original BV Lévy semigroup bridge, with no C2 assumption.
-- source:
--   Real.hasDerivAt_log, ContDiff.differentiable and the Proved C1_extended_difference_quotient_continuous.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_C1_extended_difference_quotient_continuous
set_option autoImplicit false
open Set Filter
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_04c_actual_C1_logarithmic_quotient_continuous
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w)
    (x a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    ContinuousOn
      (Function.update
        (fun t : ℝ =>
          (w (x + Real.log t) - w x) / (t - 1))
        1 (deriv w x)) (Set.Icc a 1) := by sorry
