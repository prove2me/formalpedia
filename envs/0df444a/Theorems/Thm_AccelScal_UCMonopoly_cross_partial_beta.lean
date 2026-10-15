-- Prove2me | Theorems.Thm_AccelScal_UCMonopoly_cross_partial_beta
-- name    : AccelScal.UCMonopoly.cross_partial_beta
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:47:37.744173+00:00
-- url     : https://prove2.me/theorems/44ee7cb1-7cae-4679-af10-446dc989bbc9
-- title:
--   (A.3), p. 18 — ∂²ln V/∂R∂β = λ/(λu − R)² · ∂u/∂β · (1 − β − γ) + (uλ/R)(λu − R)⁻¹ > 0
-- statement:
--   Let $T=(A,\beta,\eta,\gamma)$ satisfy the standing assumptions, $r>0$, and let $R\ge1$ with $u(R)\lambda(R)>R$. Write $\ln V(R;\beta)=\ln(u\lambda-R)-\ln(\lambda+r)$ as a function of $R$ and the scalability $\beta$. Then, with $\partial u/\partial\beta=A R^{\beta}\ln R$,
--   $$\frac{\partial^2\ln V}{\partial R\,\partial\beta}=\frac{\lambda}{(\lambda u-R)^2}\,\frac{\partial u}{\partial\beta}\,(1-\beta-\gamma)+\frac{u\lambda}{R}\,(\lambda u-R)^{-1},$$
--   and this is positive if $\beta\ne0$.
--
--   This is the increasing-differences condition behind Proposition 1(iii).
--
--   **Formalization Note** $\partial^2/\partial R\,\partial\beta$ is the $\beta$-derivative of the $R$-derivative of $\ln V$. The positivity clause keeps the paper's printed condition $\beta\neq0$.
-- source:
--   Lin, Accelerability vs. Scalability: R&D Investment Under Financial Constraints and Competition, Management Science, Articles in Advance (2022), doi:10.1287/mnsc.2022.4503, p. 18, Appendix A.2, (A.3)

import Mathlib
import Definitions.Def_AccelScal_UCMonopoly_Setting

namespace AccelScal.UCMonopoly
theorem cross_partial_beta (T : Tech) (hT : T.Standing) (r : ℝ) (hr : 0 < r) (R : ℝ)
    (hR1 : 1 ≤ R) (hRu : R < T.u R * T.lam R) :
    deriv (fun b => deriv (fun x => logV { T with β := b } r x) R) T.β =
        T.lam R / (T.lam R * T.u R - R) ^ 2 * (T.A * R ^ T.β * Real.log R) * (1 - T.β - T.γ) +
          T.u R * T.lam R / R * (T.lam R * T.u R - R)⁻¹ ∧
      (T.β ≠ 0 →
        0 < T.lam R / (T.lam R * T.u R - R) ^ 2 * (T.A * R ^ T.β * Real.log R) * (1 - T.β - T.γ) +
          T.u R * T.lam R / R * (T.lam R * T.u R - R)⁻¹) := by sorry
end AccelScal.UCMonopoly
