-- Prove2me | Theorems.Thm_CostlyPriceInterp_MarketEq_cubic_reduction
-- name    : CostlyPriceInterp.MarketEq.cubic_reduction
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:20:34.715293+00:00
-- url     : https://prove2.me/theorems/935bb96d-135a-4c6d-9f31-6f729fc99975
-- title:
--   Proof of Proposition 1, p. 56 — α·a_v(α) = a_u(α) iff α solves the cubic (18)
-- statement:
--   Assume the standing assumptions $\tau_v,\tau_\xi,\tau_\varepsilon,\tau_e,\tau_u,\tau_\eta,\gamma>0$ and let $\alpha\in\mathbb R$. Let $a_v(\alpha)$, $a_u(\alpha)$ be the expressions of Proposition 1 (with $\tau_p$ from (15)) and
--   $$f(\alpha) = (\tau_e\tau_\varepsilon+\tau_\varepsilon\tau_\eta)\alpha^3 + 2\tau_e\tau_\varepsilon\alpha^2 + (\tau_e\tau_\varepsilon+\tau_e\tau_\eta+\tau_u\tau_\varepsilon)\alpha - \tau_e\tau_u$$
--   the left-hand side of (18). Then $\alpha\, a_v(\alpha) = a_u(\alpha)$ if and only if $f(\alpha) = 0$; moreover $a_v(\alpha) > 0$.
--
--   This turns the fixed-point condition $\alpha = a_u/a_v$ of the linear equilibrium into a polynomial equation in $\alpha$, and shows that $a_v \neq 0$ holds automatically.
-- source:
--   Vives & Yang, Costly Interpretation of Asset Prices, SSRN working paper 2763813 (September 2018 version), p. 56 (PDF 55), proof of Proposition 1, 'Inserting the expressions of a's into α = a_u/a_v and simplifying yield to the cubic (18)'; cubic (18), p. 19 (PDF 21)

import Mathlib
import Definitions.Def_CostlyPriceInterp_MarketEq_Model

namespace CostlyPriceInterp.MarketEq

/-- Proof of Proposition 1, p. 56 (PDF 55): for every real α, the fixed-point condition
α = a_u/a_v, i.e. α·a_v(α) = a_u(α), holds iff α solves the cubic (18); and a_v(α) > 0. -/
theorem cubic_reduction (P : Params) (hP : P.Standing) (α : ℝ) :
    (α * avOf P α = auOf P α ↔ cubicF P α = 0) ∧ 0 < avOf P α := by sorry
end CostlyPriceInterp.MarketEq
