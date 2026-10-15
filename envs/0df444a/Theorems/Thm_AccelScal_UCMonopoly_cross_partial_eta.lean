-- Prove2me | Theorems.Thm_AccelScal_UCMonopoly_cross_partial_eta
-- name    : AccelScal.UCMonopoly.cross_partial_eta
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:47:35.596983+00:00
-- url     : https://prove2.me/theorems/78e68722-027a-4081-b472-a5b4cfb794be
-- title:
--   (A.4), p. 18 — ∂²ln V/∂R∂η = (u(1 − β − γ)/(λu − R)² − rγ/(R(λ + r)²))·∂λ/∂η, positive when γ = 0
-- statement:
--   Let $T=(A,\beta,\eta,\gamma)$ satisfy the standing assumptions, $r>0$, and let $R\ge1$ with $u(R)\lambda(R)>R$. Write $\ln V(R;\eta)=\ln(u\lambda-R)-\ln(\lambda+r)$ as a function of $R$ and the speed factor $\eta$. Then, with $\partial\lambda/\partial\eta=R^{\gamma}$,
--   $$\frac{\partial^2\ln V}{\partial R\,\partial\eta}=\Big(\frac{u(1-\beta-\gamma)}{(\lambda u-R)^2}-\frac{r\gamma}{R(\lambda+r)^2}\Big)\times\frac{\partial\lambda}{\partial\eta}.$$
--   If the project is not accelerable ($\gamma=0$), this is positive.
--
--   For $\gamma>0$ the paper notes the expression cannot be signed; that is why Proposition 1(iv) is restricted to non-accelerable projects.
--
--   **Formalization Note** $\partial^2/\partial R\,\partial\eta$ is the $\eta$-derivative of the $R$-derivative of $\ln V$. No sign is asserted for $\gamma>0$.
-- source:
--   Lin, Accelerability vs. Scalability: R&D Investment Under Financial Constraints and Competition, Management Science, Articles in Advance (2022), doi:10.1287/mnsc.2022.4503, p. 18, Appendix A.2, (A.4)

import Mathlib
import Definitions.Def_AccelScal_UCMonopoly_Setting

namespace AccelScal.UCMonopoly
theorem cross_partial_eta (T : Tech) (hT : T.Standing) (r : ℝ) (hr : 0 < r) (R : ℝ)
    (hR1 : 1 ≤ R) (hRu : R < T.u R * T.lam R) :
    deriv (fun e => deriv (fun x => logV { T with η := e } r x) R) T.η =
        (T.u R * (1 - T.β - T.γ) / (T.lam R * T.u R - R) ^ 2 -
          r * T.γ / (R * (T.lam R + r) ^ 2)) * R ^ T.γ ∧
      (T.γ = 0 →
        0 < (T.u R * (1 - T.β - T.γ) / (T.lam R * T.u R - R) ^ 2 -
          r * T.γ / (R * (T.lam R + r) ^ 2)) * R ^ T.γ) := by sorry
end AccelScal.UCMonopoly
