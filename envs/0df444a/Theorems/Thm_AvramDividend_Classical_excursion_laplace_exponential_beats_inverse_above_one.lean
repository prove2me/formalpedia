-- Prove2me | Theorems.Thm_AvramDividend_Classical_excursion_laplace_exponential_beats_inverse_above_one
-- name    : AvramDividend.Classical.excursion_laplace_exponential_beats_inverse_above_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T07:24:35.917975+00:00
-- url     : https://prove2.me/theorems/9ba334db-2f70-4a68-8be2-f2c97852a786
-- title:
--   Exponential decay beats reciprocal linear lower bounds using Laplace parameters at least one
-- statement:
--   For every r>0 and x>0 there exists a Laplace parameter θ≥1 with θexp(−θx)<r. This strengthened scalar asymptotic lemma makes the full-support contradiction usable when the ladder Bernstein exponent has only been bounded linearly for s≥1. It follows by selecting t>x from the limit texp(−t)→0 and taking θ=t/x.
-- source:
--   Pinned Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero; atTop filter; killed-ladder potential reciprocal-linear argument.

import Mathlib
open Filter Topology

theorem AvramDividend.Classical.excursion_laplace_exponential_beats_inverse_above_one
    (r x : ℝ) (hr : 0 < r) (hx : 0 < x) :
    ∃ θ : ℝ, 1 ≤ θ ∧ θ * Real.exp (-(θ * x)) < r := by sorry
