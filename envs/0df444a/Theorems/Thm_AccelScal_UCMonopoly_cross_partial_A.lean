-- Prove2me | Theorems.Thm_AccelScal_UCMonopoly_cross_partial_A
-- name    : AccelScal.UCMonopoly.cross_partial_A
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:47:52.881647+00:00
-- url     : https://prove2.me/theorems/ec9632bc-88ca-40d5-8e3b-3af7b627d6f9
-- title:
--   (A.2), p. 18 — ∂²ln V/∂R∂A = λ/(λu − R)² · ∂u/∂A · (1 − β − γ) > 0
-- statement:
--   Let $T=(A,\beta,\eta,\gamma)$ satisfy the standing assumptions, $r>0$, and let $R\ge1$ with $u(R)\lambda(R)>R$. Write $\ln V(R;A)=\ln(u\lambda-R)-\ln(\lambda+r)$ as a function of $R$ and the scaling factor $A$. Then, with $\partial u/\partial A=R^{\beta}$,
--   $$\frac{\partial^2\ln V}{\partial R\,\partial A}=\frac{\lambda}{(\lambda u-R)^2}\,\frac{\partial u}{\partial A}\,(1-\beta-\gamma)>0.$$
--
--   This is the increasing-differences condition behind Proposition 1(ii): a larger scaling factor raises the marginal return to investment intensity.
--
--   **Formalization Note** $\partial^2/\partial R\,\partial A$ is the $A$-derivative, at the given $A$, of the $R$-derivative of $\ln V$. The condition $u\lambda>R$ (equivalently $R<\bar R$) keeps the logarithm in its domain.
-- source:
--   Lin, Accelerability vs. Scalability: R&D Investment Under Financial Constraints and Competition, Management Science, Articles in Advance (2022), doi:10.1287/mnsc.2022.4503, p. 18, Appendix A.2, (A.2)

import Mathlib
import Definitions.Def_AccelScal_UCMonopoly_Setting

namespace AccelScal.UCMonopoly
theorem cross_partial_A (T : Tech) (hT : T.Standing) (r : ℝ) (hr : 0 < r) (R : ℝ)
    (hR1 : 1 ≤ R) (hRu : R < T.u R * T.lam R) :
    deriv (fun a => deriv (fun x => logV { T with A := a } r x) R) T.A =
        T.lam R / (T.lam R * T.u R - R) ^ 2 * R ^ T.β * (1 - T.β - T.γ) ∧
      0 < T.lam R / (T.lam R * T.u R - R) ^ 2 * R ^ T.β * (1 - T.β - T.γ) := by sorry
end AccelScal.UCMonopoly
