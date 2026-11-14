-- Prove2me | Theorems.Thm_CountingLLL_ReciprocalTest_source_cost_integral_bound
-- name    : CountingLLL.ReciprocalTest.source_cost_integral_bound
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:45:48.626213+00:00
-- url     : https://prove2.me/theorems/264a91fc-7832-4228-b833-2fdf094b037b
-- title:
--   Source cost integral is less than 74/25
-- statement:
--   For every $0\leq\theta\leq9/40$, the analytic bound used in the oracle-cost estimate satisfies $$\int_0^1 \frac{3t}{1-3\theta t}\,dt<\frac{74}{25}.$$ This is the uniform numerical estimate needed after bounding the paper’s weighted-change expectation by this integral; it does not establish that probabilistic bound by itself.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC #442, proof of Lemma 6.5, calls to O, p. 28, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Mathlib
open MeasureTheory
open scoped Interval

theorem CountingLLL.ReciprocalTest.source_cost_integral_bound (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 9/40) : (∫ t in (0:ℝ)..1, 3*t/(1-3*θ*t)) < (74/25:ℝ) := by sorry
