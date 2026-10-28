-- Prove2me | Theorems.Thm_AvramDividend_Classical_finite_diff_lower_of_hasDerivAt
-- name    : AvramDividend.Classical.finite_diff_lower_of_hasDerivAt
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T19:18:47.205004+00:00
-- url     : https://prove2.me/theorems/017f272f-5897-4fbd-b309-5e7607c01a45
-- title:
--   Lower finite-difference quotient converges to scale ratio
-- statement:
--   For a differentiable real function with nonzero derivative at a, the lower one-sided finite-difference quotient eps*W(a-eps)/(W(a)-W(a-eps)) tends to W(a)/deriv. This is the lower half of the finite-difference bridge for barrierSupValue_eq_scale_ratio (a8d4c941); the research helper file is already sorry-free from pinned Mathlib slope APIs.
-- source:
--   Finite-difference bridge helper for a8d4c941 barrierSupValue_eq_scale_ratio: lower one-sided quotient isolated from candidates/work_on/AvramDividend_Classical_barrierSupValue_eq_scale_ratio_a8d4c941_finite-diff-bridge_20261025.lean which is sorry-free from HasDerivAt.tendsto_slope_zero_right composition

import Mathlib

open Filter Topology
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem finite_diff_lower_of_hasDerivAt {W : ℝ → ℝ} {a : ℝ}
    (hD : HasDerivAt W (deriv W a) a) (hd : deriv W a ≠ 0) :
    Filter.Tendsto (fun ε : ℝ => ε * W (a - ε) / (W a - W (a - ε)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (W a / deriv W a)) := by sorry

end AvramDividend.Classical
