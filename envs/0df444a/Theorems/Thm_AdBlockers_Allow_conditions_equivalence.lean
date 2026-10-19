-- Prove2me | Theorems.Thm_AdBlockers_Allow_conditions_equivalence
-- name    : AdBlockers.Allow.conditions_equivalence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:15:00.510456+00:00
-- url     : https://prove2.me/theorems/bab90711-5722-4769-b3b7-cb0fb046a5f1
-- title:
--   Proof of Proposition 1, p. 44 (corrected) — the two (Allow, Allow) conditions are equivalent to a bound on β and a bound on γ/β
-- statement:
--   Let $\lambda, \mu, \beta, \gamma > 0$. Then
--
--   1. $\displaystyle \frac{\lambda}{2\beta} \ge \frac{(\lambda+\mu)(3\lambda+2\mu)^2}{2(3\lambda+4\mu)^2}$ holds if and only if $\displaystyle \beta \le \frac{\lambda(3\lambda+4\mu)^2}{(\lambda+\mu)(3\lambda+2\mu)^2}$;
--   2. $\displaystyle \frac{\lambda}{2\beta} \ge \frac{(3\lambda+2\mu)^2(\beta\lambda+\gamma\mu)}{2(3\beta\lambda+4\gamma\mu)^2}$ holds if and only if $\displaystyle \frac{\lambda + \mu\cdot\gamma/\beta}{(3\lambda+4\mu\cdot\gamma/\beta)^2} \le \frac{\lambda}{(3\lambda+2\mu)^2}$.
--
--   The left-hand sides compare the (Allow, Allow) revenue with the deviation revenues of cases 9 and 8; the right-hand sides are the thresholds on $\beta$ and $\gamma/\beta$ in Proposition 1.
--
--   **Formalization Note** The paper prints the first bound as $\lambda(3\lambda+2\mu)^2/((\lambda+\mu)(3\lambda+2\mu)^2)$, which simplifies to $\lambda/(\lambda+\mu)$ and is not equivalent to the first inequality; the correct numerator $(3\lambda+4\mu)^2$ is stated here.
-- source:
--   Despotakis, Ravi & Srinivasan, The Beneficial Effects of Ad Blockers, SSRN 3083119 (version of Nov. 28, 2017), p. 44, proof of Proposition 1 (Appendix A.1), first and second displays (corrected: (3λ+4µ)² in the first bound)

import Mathlib

namespace AdBlockers.Allow

/-- Proof of Proposition 1 (Appendix A.1), p. 44, second display (corrected): for positive
`λ, µ, β, γ`, `λ/(2β) ≥ (λ + µ)(3λ + 2µ)²/(2(3λ + 4µ)²)` iff
`β ≤ λ(3λ + 4µ)²/((λ + µ)(3λ + 2µ)²)`, and `λ/(2β) ≥ (3λ + 2µ)²(βλ + γµ)/(2(3βλ + 4γµ)²)` iff
`(λ + µ·γ/β)/(3λ + 4µ·γ/β)² ≤ λ/(3λ + 2µ)²`. -/
theorem conditions_equivalence (lam μ β γ : ℝ) (hlam : 0 < lam) (hμ : 0 < μ) (hβ : 0 < β)
    (hγ : 0 < γ) :
    ((lam + μ) * (3 * lam + 2 * μ) ^ 2 / (2 * (3 * lam + 4 * μ) ^ 2) ≤ lam / (2 * β) ↔
        β ≤ lam * (3 * lam + 4 * μ) ^ 2 / ((lam + μ) * (3 * lam + 2 * μ) ^ 2)) ∧
      ((3 * lam + 2 * μ) ^ 2 * (β * lam + γ * μ) / (2 * (3 * β * lam + 4 * γ * μ) ^ 2) ≤
          lam / (2 * β) ↔
        (lam + μ * (γ / β)) / (3 * lam + 4 * μ * (γ / β)) ^ 2 ≤ lam / (3 * lam + 2 * μ) ^ 2) := by sorry

end AdBlockers.Allow
