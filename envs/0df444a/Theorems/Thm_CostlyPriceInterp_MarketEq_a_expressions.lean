-- Prove2me | Theorems.Thm_CostlyPriceInterp_MarketEq_a_expressions
-- name    : CostlyPriceInterp.MarketEq.a_expressions
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:20:36.784052+00:00
-- url     : https://prove2.me/theorems/b3d1e9dc-f8a0-4677-9285-aec521f6cfd3
-- title:
--   Proof of Proposition 1, p. 56 — β_s + β_p and β_p(α + 1) + β_z are the closed forms of a_v, a_u
-- statement:
--   Assume the standing assumptions $\tau_v,\tau_\xi,\tau_\varepsilon,\tau_e,\tau_u,\tau_\eta,\gamma>0$, let $\alpha\in\mathbb R$, let $(\beta_s,\beta_p,\beta_z) = \Sigma(\alpha)^{-1}c$ be the conditional-mean coefficients of (16), and let $\tau_p = \tau_p(\alpha)$ be given by (15). Then
--   $$\beta_s + \beta_p = \frac{\tau_\varepsilon+\tau_p}{\tau_v+\tau_\varepsilon+\tau_p}, \qquad \beta_p(\alpha+1)+\beta_z = \frac{\tau_p}{\tau_v+\tau_\varepsilon+\tau_p}\cdot\frac{\tau_u(\tau_e+\alpha\tau_e+\alpha\tau_\eta)}{\tau_e\tau_u+\tau_e\tau_\eta+\tau_u\tau_\eta}.$$
--
--   The right-hand sides are the expressions of $a_v$ and $a_u$ in Proposition 1, as functions of $\alpha$.
-- source:
--   Vives & Yang, Costly Interpretation of Asset Prices, SSRN working paper 2763813 (September 2018 version), p. 56 (PDF 55), proof of Proposition 1, 'Plugging the expressions of β's into the above two conditions leads to the expressions of a's in Proposition 1'; the expressions from Proposition 1, p. 19 (PDF 21)

import Mathlib
import Definitions.Def_CostlyPriceInterp_MarketEq_Model

namespace CostlyPriceInterp.MarketEq

/-- Proof of Proposition 1, p. 56 (PDF 55): plugging the β's into a_v = β_s + β_p and
a_u = β_p(α + 1) + β_z gives the expressions of a_v and a_u in Proposition 1, for every real α. -/
theorem a_expressions (P : Params) (hP : P.Standing) (α : ℝ) :
    bayesCoef P α 0 + bayesCoef P α 1 = avOf P α ∧
      bayesCoef P α 1 * (α + 1) + bayesCoef P α 2 = auOf P α := by sorry
end CostlyPriceInterp.MarketEq
