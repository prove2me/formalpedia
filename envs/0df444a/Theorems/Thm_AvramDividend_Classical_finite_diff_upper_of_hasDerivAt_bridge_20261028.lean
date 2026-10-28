-- Prove2me | Theorems.Thm_AvramDividend_Classical_finite_diff_upper_of_hasDerivAt_bridge_20261028
-- name    : AvramDividend.Classical.finite_diff_upper_of_hasDerivAt_bridge_20261028
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T17:07:14.081449+00:00
-- url     : https://prove2.me/theorems/1b00aa99-afc2-4fa2-bd35-b0eb35ce9315
-- title:
--   One-sided finite-difference quotient limit from HasDerivAt (upper)
-- statement:
--   For a real function with derivative at a and nonzero derivative, the upper one-sided finite-difference quotient eps * W(a+eps) / (W(a+eps) - W a) tends to W a / deriv W a as eps approaches 0 from above. Symmetric upper companion to the lower bridge.
-- source:
--   Companion to the lower finite-difference bridge for barrierSupValue_eq_scale_ratio. Same pure-analysis provenance, no stochastic dependencies.

import Mathlib
open Filter Topology

theorem AvramDividend.Classical.finite_diff_upper_of_hasDerivAt_bridge_20261028
    {W : ℝ → ℝ} {a : ℝ}
    (hD : HasDerivAt W (deriv W a) a) (hd : deriv W a ≠ 0) :
    Filter.Tendsto (fun ε : ℝ => ε * W (a + ε) / (W (a + ε) - W a))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (W a / deriv W a)) := by sorry
