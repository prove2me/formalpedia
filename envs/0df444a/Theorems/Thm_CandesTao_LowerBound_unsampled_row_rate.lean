-- Prove2me | Theorems.Thm_CandesTao_LowerBound_unsampled_row_rate
-- name    : CandesTao.LowerBound.unsampled_row_rate
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T19:44:22.934985+00:00
-- url     : https://prove2.me/theorems/5bd5a310-d88b-427d-a090-7bd1c48be155
-- title:
--   Section II — $(1-\pi)^n \ge 1-\delta$ with $\delta < 1/2$ forces $\pi \le 2\delta/n$
-- statement:
--   Let $n \ge 1$ be an integer, $\pi \in [0,1]$ and $0 < \delta < 1/2$. If
--
--   $$(1-\pi)^n \ge 1-\delta,$$
--
--   then
--
--   $$\pi \le \frac{2\delta}{n}.$$
--
--   In the lower-bound argument of Candès and Tao, $\pi$ is the probability that a fixed row (or a fixed row of a diagonal block) is unsampled and $(1-\pi)^n$ the probability that all $n$ of them are sampled. The implication turns "any method succeeds with probability at least $1-\delta$" into an upper bound on $\pi$, hence a lower bound on the sampling rate.
-- source:
--   Candès & Tao, The Power of Convex Relaxation: Near-Optimal Matrix Completion, IEEE Trans. Inf. Theory 56(5), 2010, p. 2059, Section II, displays (1 − π₀)^n ≥ 1 − δ and π₀ ≤ 2δ/n

import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace CandesTao.LowerBound

theorem unsampled_row_rate (n : ℕ) (π δ : ℝ)
    (hn : 1 ≤ n) (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1) (hδ : 0 < δ) (hδ' : δ < 1 / 2)
    (h : (1 - π) ^ n ≥ 1 - δ) :
    π ≤ 2 * δ / n := by sorry

end CandesTao.LowerBound
