-- Prove2me | Theorems.Thm_AdBlockers_Allow_g_strictAntiOn
-- name    : AdBlockers.Allow.g_strictAntiOn
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:15:00.715176+00:00
-- url     : https://prove2.me/theorems/91689efd-721e-4e54-93d3-690afd225686
-- title:
--   Proof of Proposition 1, p. 44 — g(x) = (λ+µx)/(3λ+4µx)² is decreasing on [0, ∞)
-- statement:
--   Let $\lambda, \mu > 0$. The function
--   $$
--   g(x) = \frac{\lambda + \mu x}{(3\lambda + 4\mu x)^2}
--   $$
--   is strictly decreasing on $[0, \infty)$.
--
--   Applied to $x = \gamma/\beta$, this turns the second condition of Proposition 1 into a lower threshold on $\gamma/\beta$.
--
--   **Formalization Note** Monotonicity is stated on $[0,\infty)$ only: $g$ has a pole at $x = -3\lambda/(4\mu)$.
-- source:
--   Despotakis, Ravi & Srinivasan, The Beneficial Effects of Ad Blockers, SSRN 3083119 (version of Nov. 28, 2017), p. 44, proof of Proposition 1 (Appendix A.1), the function g

import Mathlib

namespace AdBlockers.Allow

/-- Proof of Proposition 1 (Appendix A.1), p. 44: for positive `λ, µ`, the function
`g(x) = (λ + µx)/(3λ + 4µx)²` is strictly decreasing on `[0, ∞)`. -/
theorem g_strictAntiOn (lam μ : ℝ) (hlam : 0 < lam) (hμ : 0 < μ) :
    StrictAntiOn (fun x : ℝ => (lam + μ * x) / (3 * lam + 4 * μ * x) ^ 2) (Set.Ici 0) := by sorry

end AdBlockers.Allow
