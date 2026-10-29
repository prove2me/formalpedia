-- Prove2me | Theorems.Thm_AvramDividend_Classical_finite_diff_lower_scale_ratio_limit_of_hasDerivAt
-- name    : AvramDividend.Classical.finite_diff_lower_scale_ratio_limit_of_hasDerivAt
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T22:00:35.426985+00:00
-- url     : https://prove2.me/theorems/a76198af-e0e4-40b4-81b9-1a8200e05599
-- title:
--   Lower one-sided finite-difference scale ratio limit from differentiability
-- statement:
--   For a real function differentiable at a with nonzero derivative, the lower one-sided quotient eps * W(a-eps) / (W(a)-W(a-eps)) tends to W(a)/deriv as eps approaches 0 from above. This is the exact finite-difference bridge needed for the barrierSupValue scale-ratio limit.
-- source:
--   Isolates the pure-analysis finite-difference step of parent AvramDividend.Classical.barrierSupValue_eq_scale_ratio (a8d4c941): the stopped-renewal bounds reduce the parent to this one-sided quotient limit plus derivative positivity (4052). The child takes no Open Prove2Me premises, only HasDerivAt and nonzero derivative, so the decomposition is acyclic. Proved helper source exists locally in candidates/work_on/AvramDividend_Classical_barrierSupValue_eq_scale_ratio_a8d4c941_finite-diff-bridge_20261025.lean (sorry-free, unverified).

import Mathlib

open Filter Topology

theorem AvramDividend.Classical.finite_diff_lower_scale_ratio_limit_of_hasDerivAt
    {W : ℝ → ℝ} {a : ℝ}
    (hD : HasDerivAt W (deriv W a) a) (hd : deriv W a ≠ 0) :
    Filter.Tendsto (fun ε : ℝ => ε * W (a - ε) / (W a - W (a - ε))) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (W a / deriv W a)) := by sorry
