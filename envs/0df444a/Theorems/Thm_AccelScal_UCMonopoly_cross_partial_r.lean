-- Prove2me | Theorems.Thm_AccelScal_UCMonopoly_cross_partial_r
-- name    : AccelScal.UCMonopoly.cross_partial_r
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:47:38.776963+00:00
-- url     : https://prove2.me/theorems/4a2a89d9-8b21-4b12-bca7-30bec3dd960e
-- title:
--   (A.6), p. 18 — ∂²ln V/∂R∂r = λ′/(λ + r)² > 0 when the project is accelerable
-- statement:
--   Let $T=(A,\beta,\eta,\gamma)$ satisfy the standing assumptions, $r>0$, and let $R\ge1$ with $u(R)\lambda(R)>R$. Write $\ln V(R;r)=\ln(u\lambda-R)-\ln(\lambda+r)$ as a function of $R$ and the discount rate $r$. Then
--   $$\frac{\partial^2\ln V}{\partial R\,\partial r}=\frac{\lambda'(R)}{(\lambda(R)+r)^2},$$
--   and this is positive if the project is accelerable ($\gamma>0$).
--
--   This is the increasing-differences condition behind the second half of Proposition 1(v).
--
--   **Formalization Note** $\lambda'(R)$ is the derivative of $R\mapsto\eta R^{\gamma}$ at $R$ (Lean's `deriv`), not its closed form $\eta\gamma R^{\gamma-1}$. $\partial^2/\partial R\,\partial r$ is the $r$-derivative of the $R$-derivative of $\ln V$.
-- source:
--   Lin, Accelerability vs. Scalability: R&D Investment Under Financial Constraints and Competition, Management Science, Articles in Advance (2022), doi:10.1287/mnsc.2022.4503, p. 18, Appendix A.2, (A.6)

import Mathlib
import Definitions.Def_AccelScal_UCMonopoly_Setting

namespace AccelScal.UCMonopoly
theorem cross_partial_r (T : Tech) (hT : T.Standing) (r : ℝ) (hr : 0 < r) (R : ℝ)
    (hR1 : 1 ≤ R) (hRu : R < T.u R * T.lam R) :
    deriv (fun s => deriv (fun x => logV T s x) R) r = deriv T.lam R / (T.lam R + r) ^ 2 ∧
      (0 < T.γ → 0 < deriv T.lam R / (T.lam R + r) ^ 2) := by sorry
end AccelScal.UCMonopoly
