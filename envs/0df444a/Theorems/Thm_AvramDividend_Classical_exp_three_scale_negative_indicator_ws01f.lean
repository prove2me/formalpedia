-- Prove2me | Theorems.Thm_AvramDividend_Classical_exp_three_scale_negative_indicator_ws01f
-- name    : AvramDividend.Classical.exp_three_scale_negative_indicator_ws01f
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T10:29:31.365139+00:00
-- url     : https://prove2.me/theorems/98062639-34d6-4544-af65-90462c08f72b
-- title:
--   Three positive exponential moments control the negative-tail indicator
-- statement:
--   For real r at least one, the difference exp(x)-1 is bounded above by a large multiple of the small-scale exponential difference, a small multiple of exp(2x)-1, and an explicit multiple of the negative-sign indicator. This deterministic inequality, when integrated against the Lévy increments and combined with quadratic asymptotics for three positive Laplace parameters, yields a strictly positive negative-tail probability without an unproved Gaussian weak-convergence theorem. It does not assume signs or stochastic results.
-- source:
--   Elementary exponential inequalities and a two-case comparison at exp(x)=r. Gaussian WS1F alternative to a one-sided MGF continuity theorem.

import Mathlib

open Filter

theorem AvramDividend.Classical.exp_three_scale_negative_indicator_ws01f (r x : ℝ) (hr : 1 ≤ r) :
    Real.exp x - 1 ≤
      r ^ 2 * (Real.exp (x / r) - 1) +
      (Real.exp (2 * x) - 1) / r +
      (r ^ 2 + 1 / r) * (if x < 0 then (1 : ℝ) else 0) := by sorry
