-- Prove2me | Theorems.Thm_AvramDividend_Classical_excursion_inverse_laplace_lower_bound_excludes_exponential_envelope
-- name    : AvramDividend.Classical.excursion_inverse_laplace_lower_bound_excludes_exponential_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T07:14:02.412998+00:00
-- url     : https://prove2.me/theorems/57b0697b-84ce-4829-8a48-60e2b89e61eb
-- title:
--   An inverse-linear Laplace lower bound excludes any positive-height exponential support gap
-- statement:
--   Suppose a Laplace transform has the reciprocal-linear lower bound c/θ for every θ>0 but is also bounded by C exp(−θx) for a positive support gap x>0. No such bounds can coexist because θ exp(−θx) tends to zero. This deterministic contradiction is precisely the full-support argument for killed-subordinator ladder-potential measures once their transform 1/F(θ) has a c/θ lower bound and total mass at most C.
-- source:
--   Proved excursion_laplace_exponential_beats_inverse; basic ordered field inequalities; Esscher ladder-potential support argument.

import Mathlib

theorem AvramDividend.Classical.excursion_inverse_laplace_lower_bound_excludes_exponential_envelope
    (c C x : ℝ) (hc : 0 < c) (hC : 0 ≤ C) (hx : 0 < x)
    (henvelope : ∀ θ : ℝ, 0 < θ → c / θ ≤ C * Real.exp (-(θ * x))) :
    False := by sorry
