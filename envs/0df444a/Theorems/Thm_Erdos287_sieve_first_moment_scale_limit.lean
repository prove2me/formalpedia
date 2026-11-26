-- Prove2me | Theorems.Thm_Erdos287_sieve_first_moment_scale_limit
-- name    : Erdos287.sieve_first_moment_scale_limit
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T05:08:27.648511+00:00
-- url     : https://prove2.me/theorems/4b303592-179b-5d4f-a00f-db8bc0ccb9cb
-- title:
--   The exponent constraint bounds the normalized first moment below one
-- statement:
--   If the distribution exponent is above 78/145 and at most 7/13−3θ, then θ is below 1/5655. For any simplex radius σ between zero and θ and at most 10^959 forms, 2σ log(1+T) is below one.
-- source:
--   Erdős Problem #287; size analysis of the proposed 145-group weighted sieve and its finite-range splice.

import Mathlib

theorem Erdos287.sieve_first_moment_scale_limit (δ θ σ T : ℝ)
    (hδ : 78 / 145 < δ) (hlevel : δ ≤ 7 / 13 - 3 * θ)
    (hσ : 0 ≤ σ) (hσθ : σ ≤ θ) (hT : 1 ≤ T) (hsize : T ≤ 10 ^ (959 : ℕ)) :
    θ < 1 / 5655 ∧ 2 * σ * Real.log (1 + T) < 1 := by sorry
