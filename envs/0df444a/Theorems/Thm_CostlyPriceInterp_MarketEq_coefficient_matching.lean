-- Prove2me | Theorems.Thm_CostlyPriceInterp_MarketEq_coefficient_matching
-- name    : CostlyPriceInterp.MarketEq.coefficient_matching
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:20:27.630996+00:00
-- url     : https://prove2.me/theorems/3a6fe87c-9bfd-4b32-b0ab-c3c7cc6747a5
-- title:
--   Proof of Proposition 1, p. 56 — market clearing iff a_v = β_s + β_p and a_u = β_p(α + 1) + β_z
-- statement:
--   Assume the standing assumptions $\tau_v,\tau_\xi,\tau_\varepsilon,\tau_e,\tau_u,\tau_\eta,\gamma>0$. For real numbers $a_v, a_u$ put $\alpha = a_u/a_v$ and let $(\beta_s,\beta_p,\beta_z) = \Sigma(\alpha)^{-1}c$ be the conditional-mean coefficients of (16) at that $\alpha$. Then $(a_v,a_u)$ is a linear financial market equilibrium — $a_v\ne 0$ and aggregate CARA demand at the price $\tilde p = a_v\tilde v + a_u\tilde u$ vanishes for every $(\tilde v,\tilde u)$ — if and only if $a_v \neq 0$ and
--   $$a_v = \beta_s + \beta_p \qquad\text{and}\qquad a_u = \beta_p(\alpha+1) + \beta_z.$$
--
--   This is the coefficient-comparison step: market clearing becomes two scalar equations in the price coefficients.
-- source:
--   Vives & Yang, Costly Interpretation of Asset Prices, SSRN working paper 2763813 (September 2018 version), p. 56 (PDF 55), proof of Proposition 1, 'Inserting the expression of E(ṽ|s̃_i, s̃_{pz,i}) and comparing with the coefficients of the conjectured price function (11), we have: a_v = β_s + β_p and a_u = β_p(α + 1) + β_z'

import Mathlib
import Definitions.Def_CostlyPriceInterp_MarketEq_Model

namespace CostlyPriceInterp.MarketEq

/-- Proof of Proposition 1, p. 56 (PDF 55): market clearing at the conjectured price (11) holds for
every (ṽ, ũ) iff a_v = β_s + β_p and a_u = β_p(α + 1) + β_z, where α = a_u/a_v and the β's are those
of (16) at that α. -/
theorem coefficient_matching (P : Params) (hP : P.Standing) (av au : ℝ) :
    IsLinearEq P av au ↔
      av ≠ 0 ∧
        av = bayesCoef P (au / av) 0 + bayesCoef P (au / av) 1 ∧
        au = bayesCoef P (au / av) 1 * (au / av + 1) + bayesCoef P (au / av) 2 := by sorry
end CostlyPriceInterp.MarketEq
