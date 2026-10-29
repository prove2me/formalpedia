-- Prove2me | Theorems.Thm_AvramDividend_Classical_finite_diff_upper_scale_ratio_limit_of_hasDerivAt
-- name    : AvramDividend.Classical.finite_diff_upper_scale_ratio_limit_of_hasDerivAt
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T22:07:43.463108+00:00
-- url     : https://prove2.me/theorems/d072d38d-130a-4430-8b15-f2b5d0a2c268
-- title:
--   Upper one-sided finite-difference scale ratio limit from differentiability
-- statement:
--   For a real function differentiable at a with nonzero derivative, the upper one-sided quotient eps * W(a+eps) / (W(a+eps)-W(a)) tends to W(a)/deriv as eps approaches 0 from above. This is the upper half of the exact finite-difference bridge needed for the barrierSupValue scale-ratio limit.
-- source:
--   Isolates the pure-analysis upper finite-difference step of parent AvramDividend.Classical.barrierSupValue_eq_scale_ratio (a8d4c941), symmetric to the published lower sibling. The child takes no Open Prove2Me premises, only HasDerivAt and nonzero derivative, so the decomposition is acyclic. Proved helper source exists locally in candidates/work_on/AvramDividend_Classical_barrierSupValue_eq_scale_ratio_a8d4c941_finite-diff-bridge_20261025.lean (sorry-free, unverified).

import Mathlib

open Filter Topology

theorem AvramDividend.Classical.finite_diff_upper_scale_ratio_limit_of_hasDerivAt
    {W : ℝ → ℝ} {a : ℝ}
    (hD : HasDerivAt W (deriv W a) a) (hd : deriv W a ≠ 0) :
    Filter.Tendsto (fun ε : ℝ => ε * W (a + ε) / (W (a + ε) - W a)) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (W a / deriv W a)) := by sorry
