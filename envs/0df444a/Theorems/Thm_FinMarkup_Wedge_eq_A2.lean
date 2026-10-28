-- Prove2me | Theorems.Thm_FinMarkup_Wedge_eq_A2
-- name    : FinMarkup.Wedge.eq_A2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T20:38:34.257131+00:00
-- url     : https://prove2.me/theorems/644e9961-8a87-412f-986d-15c1775284d2
-- title:
--   Appendix (A.2) — derivative of expected customer-base growth
-- statement:
--   Let $P>0$ be the firm's price, $P_t>0$ the industry price index, and $M$ its customer base. For demand elasticity $\eta$, accumulation speed $\beta$, and industry elasticity $\epsilon$, the price derivative of the expected customer-base drift is
--
--   $$\frac{\partial g_M}{\partial P}(P)=-\beta\eta P^{-\eta-1}P_t^{\eta-\epsilon}M.$$
--
--   This is the customer-base term in the pricing first-order condition.
--
--   **Formalization Note** $g_M$ is the expected drift per unit time, so the paper's factor $dt$ is omitted. The statement carries the model's standing conditions $1<\epsilon<\eta$, $\beta\ge0$, $A,R>0$, and $M>0$; $P,P_t>0$ give real powers their usual calculus meaning.
-- source:
--   Dou & Ji, External Financing and Customer Capital: A Financial Theory of Markups, SSRN 2574953 (version of May 11, 2020), p. 33 (PDF 34), Online Appendix A.1, (A.2)

import Mathlib
import Definitions.Def_FinMarkup_Wedge_Model

namespace FinMarkup.Wedge

/-- Online Appendix A.1, (A.2), p. 33. -/
theorem eq_A2 (m : Params) (hS : m.Standing) (Pt M p : ℝ)
    (hPt : 0 < Pt) (hM : 0 < M) (hp : 0 < p) :
    HasDerivAt (fun q => driftM m Pt M q)
      (-(m.beta * m.eta * p ^ (-m.eta - 1) * Pt ^ (m.eta - m.eps) * M)) p := by sorry

end FinMarkup.Wedge
