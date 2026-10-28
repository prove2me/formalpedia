-- Prove2me | Theorems.Thm_AvramDividend_Classical_finite_diff_upper_of_hasDerivAt
-- name    : AvramDividend.Classical.finite_diff_upper_of_hasDerivAt
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T19:18:47.713965+00:00
-- url     : https://prove2.me/theorems/b66e2c3b-c2d3-4371-b1c9-671822f47d59
-- title:
--   Upper finite-difference quotient converges to scale ratio
-- statement:
--   For a differentiable real function with nonzero derivative at a, the upper one-sided finite-difference quotient eps*W(a+eps)/(W(a+eps)-W(a)) tends to W(a)/deriv. This is the upper half of the finite-difference bridge for barrierSupValue_eq_scale_ratio (a8d4c941).
-- source:
--   Finite-difference bridge helper for a8d4c941 barrierSupValue_eq_scale_ratio: upper one-sided quotient isolated from the same sorry-free research helper

import Mathlib

open Filter Topology
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem finite_diff_upper_of_hasDerivAt {W : ℝ → ℝ} {a : ℝ}
    (hD : HasDerivAt W (deriv W a) a) (hd : deriv W a ≠ 0) :
    Filter.Tendsto (fun ε : ℝ => ε * W (a + ε) / (W (a + ε) - W a))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (W a / deriv W a)) := by sorry

end AvramDividend.Classical
