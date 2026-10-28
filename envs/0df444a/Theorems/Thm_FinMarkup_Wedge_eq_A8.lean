-- Prove2me | Theorems.Thm_FinMarkup_Wedge_eq_A8
-- name    : FinMarkup.Wedge.eq_A8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T20:38:42.523558+00:00
-- url     : https://prove2.me/theorems/ac5ba2ae-9991-4385-a6e7-38e5893e23b9
-- title:
--   Appendix (A.8) — the stationary price expressed as a markup
-- statement:
--   Let $1<\epsilon<\eta$, $\beta\ge0$, $A>0$, $R>0$, $\mu\ge0$, and $\nu>0$. Substituting the price from (A.6) into the price-to-marginal-cost markup and using the wedge $\Omega=(\beta A/R)(\mu/\nu)$ gives
--
--   $$\Lambda\!\left(\frac{\eta}{\eta-1}\frac{R}{A}-\frac{\beta\eta}{\eta-1}\frac{\mu}{\nu}\right)
--     =\frac{\eta}{\eta-1}(1-\Omega).$$
--
--   This is the algebraic conversion from the appendix's price formula to Proposition 3.1's markup formula.
--
--   **Formalization Note** The theorem carries the model's standing conditions and uses the wedge definition in (3.2). Appendix (A.7) prints the reciprocal $\nu/\mu$, which is inconsistent with both (3.2) and the substitution into (A.6). This statement does not assert that the displayed price is positive or optimal; those are part of the main proposition.
-- source:
--   Dou & Ji, External Financing and Customer Capital: A Financial Theory of Markups, SSRN 2574953 (version of May 11, 2020), p. 34 (PDF 35), Online Appendix A.1, (A.8), using (3.2) on p. 14 (PDF 15) in place of the reversed ratio in (A.7)

import Mathlib
import Definitions.Def_FinMarkup_Wedge_Model

namespace FinMarkup.Wedge

/-- Online Appendix A.1, (A.8), p. 34, using wedge (3.2). -/
theorem eq_A8 (m : Params) (hS : m.Standing) (mu nu : ℝ)
    (hmu : 0 ≤ mu) (hnu : 0 < nu) :
    markup m (m.eta / (m.eta - 1) * (m.R / m.A) -
      m.beta * m.eta / (m.eta - 1) * (mu / nu)) =
      m.eta / (m.eta - 1) * (1 - wedge m mu nu) := by sorry

end FinMarkup.Wedge
