-- Prove2me | Theorems.Thm_Apery_tendsto_pow_mul_exp_neg_sq_of_pos
-- name    : Apery.tendsto_pow_mul_exp_neg_sq_of_pos
-- status  : Open
-- author  : @tomasz
-- created : 2026-10-01T10:49:34.903986+00:00
-- url     : https://prove2.me/theorems/71065187-91ca-4019-97b0-3bfa261d68e3
-- title:
--   Quadratic exponential decay dominates every fixed denominator
-- statement:
--   For every real $c>0$ and every positive natural number $b$,
--   $$\lim_{n\to\infty}b^{37n}e^{-cn^2}=0.$$
--   This supplies the decay hypothesis of the polynomial irrationality criterion for any strictly positive quadratic decay rate, including the rate provided by the repository's modified normalization.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Criterion.lean#L98-L119

import Mathlib

open Polynomial Filter Topology MeasureTheory

namespace Apery

theorem tendsto_pow_mul_exp_neg_sq_of_pos {c : ℝ} (hc : 0 < c) (b : ℕ) (hb : 0 < b) :
    Tendsto (fun n : ℕ => (b : ℝ) ^ (37 * n) * Real.exp (-c * (n : ℝ) ^ 2)) atTop (𝓝 0) := by sorry

end Apery
