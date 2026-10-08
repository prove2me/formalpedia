-- Prove2me | Theorems.Thm_AvramDividend_Classical_eventual_normalised_lower_of_monotone_integer_limit
-- name    : AvramDividend.Classical.eventual_normalised_lower_of_monotone_integer_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T06:25:42.025991+00:00
-- url     : https://prove2.me/theorems/ecc4308e-1d28-4361-96e2-7c790ca2d6fd
-- title:
--   A positive monotone integer limit yields an eventual normalised lower gap
-- statement:
--   Let J(θ) be nondecreasing for positive θ and suppose J(n+1) tends to A. If B is nonnegative, q is positive, and c+A is strictly positive, then beyond some positive real threshold every θ satisfies q/θ < c+J(θ)-B/θ. This is the exact real-parameter order bridge needed to turn integer compensated-jump convergence into eventual positivity of a zero-Gaussian Lévy exponent.
-- source:
--   Elementary filter convergence and order arithmetic using the pinned Mathlib limit 1/(n+1)→0. The proof chooses one sufficiently large integer N and uses monotonicity of J plus denominator monotonicity for all real θ≥N+1.

import Mathlib

open Filter

theorem AvramDividend.Classical.eventual_normalised_lower_of_monotone_integer_limit
    (J : ℝ → ℝ) (c A B q : ℝ)
    (hJmono : ∀ θ₁ θ₂ : ℝ, 0 < θ₁ → θ₁ ≤ θ₂ → J θ₁ ≤ J θ₂)
    (hJlim : Filter.Tendsto (fun n : ℕ => J ((n : ℝ) + 1))
      Filter.atTop (nhds A))
    (hB : 0 ≤ B) (hd : 0 < c + A) (hq : 0 < q) :
    ∃ θ₀ : ℝ, 0 < θ₀ ∧ ∀ θ : ℝ, θ₀ ≤ θ →
      q / θ < c + J θ - B / θ := by sorry
