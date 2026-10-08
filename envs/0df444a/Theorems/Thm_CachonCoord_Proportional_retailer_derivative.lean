-- Prove2me | Theorems.Thm_CachonCoord_Proportional_retailer_derivative
-- name    : CachonCoord.Proportional.retailer_derivative
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:44:01.525632+00:00
-- url     : https://prove2.me/theorems/0f3856aa-9fcd-41c5-9707-a5575c21d49f
-- title:
--   p. 51 — the derivative in the first order condition: ∂π_i/∂q_i = (p − w) − (p − b)[(q_i/q)F(q) + (q_−i/q)(1/q)∫₀^q F]
-- statement:
--   Let $q_i > 0$, $q_{-i} \ge 0$ and $q = q_i + q_{-i}$. The retailer's profit is differentiable in his own order at $q_i$, with
--
--   $$
--   \frac{\partial \pi_i(q_i, q_{-i})}{\partial q_i} = (p-w) - (p-b)\left[\frac{q_i}{q}F(q) + \frac{q_{-i}}{q}\cdot\frac1q\int_0^q F(x)\,dx\right].
--   $$
--
--   Multiplying by $q/(p-b)$ gives the expression the book sets to zero in the first order condition on p. 51.
--
--   **Formalization Note** The page prints the first order condition as "$\partial\pi_i(q_i,q_j)/q_i = q^*\frac{p-w}{p-b} - q_i^*F(q^*) - q_{-i}^*\big(\frac1{q^*}\int_0^{q^*}F\big) = 0$": the right side is the derivative multiplied by $q^*/(p-b)$, a harmless rescaling for the equation $=0$ but not an identity. The Lean states the derivative itself. The hypotheses on the demand law are the chapter's standing assumptions (p. 7), carried by the model.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.5.1, p. 51 (the first order condition display; printed slip in its left side)

import Mathlib
import Definitions.Def_CachonCoord_Proportional_Demand
import Definitions.Def_CachonCoord_Proportional_Nash
import Definitions.Def_CachonCoord_Proportional_Game

namespace CachonCoord.Proportional

/-- p. 51, the derivative in the first order condition (stated correctly; the page prints it
multiplied by `q/(p − b)`): for `q_i > 0` and `q_{−i} ≥ 0`, with `q = q_i + q_{−i}`,
`∂π_i/∂q_i = (p − w) − (p − b) [(q_i/q) F(q) + (q_{−i}/q) (1/q) ∫_0^q F(x) dx]`. -/
theorem retailer_derivative (M : Model) (w b x s : ℝ) (hx : 0 < x) (hs : 0 ≤ s) :
    HasDerivAt (fun y => M.retailerProfit w b y s)
      ((M.p - w) - (M.p - b) *
        (x / (x + s) * M.F (x + s) + s / (x + s) * M.avgF (x + s))) x := by sorry

end CachonCoord.Proportional
