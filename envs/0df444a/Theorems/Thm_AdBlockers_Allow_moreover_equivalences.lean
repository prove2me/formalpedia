-- Prove2me | Theorems.Thm_AdBlockers_Allow_moreover_equivalences
-- name    : AdBlockers.Allow.moreover_equivalences
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:15:03.194617+00:00
-- url     : https://prove2.me/theorems/963459af-578a-4187-b84b-932511335042
-- title:
--   Proof of Proposition 1, p. 44 — λ/(2β) beats the benchmark profits iff γ/β ≥ 2 + µ/λ and β ≤ λ/(λ+µ)
-- statement:
--   Let $\lambda, \mu, \beta, \gamma > 0$. Then
--
--   1. $\displaystyle \frac{\lambda}{2\beta} \ge \frac{(\lambda+\mu)^2}{2(\beta\lambda+\gamma\mu)}$ holds if and only if $\displaystyle \frac{\gamma}{\beta} \ge 2 + \frac{\mu}{\lambda}$;
--   2. $\displaystyle \frac{\lambda}{2\beta} \ge \frac{\lambda+\mu}{2}$ holds if and only if $\displaystyle \beta \le \frac{\lambda}{\lambda+\mu}$.
--
--   The left-hand sides compare the (Allow, Allow) revenue with the benchmark (Ads, Ads) and (Fee, Fee) revenues.
-- source:
--   Despotakis, Ravi & Srinivasan, The Beneficial Effects of Ad Blockers, SSRN 3083119 (version of Nov. 28, 2017), p. 44, proof of Proposition 1 (Appendix A.1), last display

import Mathlib

namespace AdBlockers.Allow

/-- Proof of Proposition 1 (Appendix A.1), p. 44, last display: for positive `λ, µ, β, γ`,
`λ/(2β) ≥ (λ + µ)²/(2(βλ + γµ))` iff `γ/β ≥ 2 + µ/λ`, and `λ/(2β) ≥ (λ + µ)/2` iff
`β ≤ λ/(λ + µ)`. -/
theorem moreover_equivalences (lam μ β γ : ℝ) (hlam : 0 < lam) (hμ : 0 < μ) (hβ : 0 < β)
    (hγ : 0 < γ) :
    ((lam + μ) ^ 2 / (2 * (β * lam + γ * μ)) ≤ lam / (2 * β) ↔ 2 + μ / lam ≤ γ / β) ∧
      ((lam + μ) / 2 ≤ lam / (2 * β) ↔ β ≤ lam / (lam + μ)) := by sorry

end AdBlockers.Allow
