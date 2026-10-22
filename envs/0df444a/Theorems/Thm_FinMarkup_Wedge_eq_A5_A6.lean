-- Prove2me | Theorems.Thm_FinMarkup_Wedge_eq_A5_A6
-- name    : FinMarkup.Wedge.eq_A5_A6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T20:38:37.185933+00:00
-- url     : https://prove2.me/theorems/6194bec5-611d-46b0-a31d-dc2429cc18c1
-- title:
--   Appendix (A.5)–(A.6) — the pricing first-order condition and price formula
-- statement:
--   Suppose $1<\epsilon<\eta$, $\beta\ge0$, $A,R>0$, $P>0$, $P_t>0$, $M>0$, and marginal values $\mu\ge0$ and $\nu>0$ of customer base and liquidity. Using the drift derivatives in (A.2) and (A.4), the pricing first-order condition is equivalent to
--
--   $$\mu\frac{\partial g_M}{\partial P}(P)+\nu\frac{\partial g_W}{\partial P}(P)=0
--   \quad\Longleftrightarrow\quad
--   P=\frac{\eta}{\eta-1}\frac{R}{A}-\frac{\beta\eta}{\eta-1}\frac{\mu}{\nu}.$$
--
--   This identifies the only positive stationary price when the displayed expression is positive. The main proposition additionally establishes global optimality under its domain assumptions.
--
--   **Formalization Note** The derivatives are expanded as the literal expressions in (A.2) and (A.4); the theorem states their zero condition. Positive $P,P_t,M,\nu$ and $\eta>1$ permit cancellation and division. The other standing conditions are carried from the model. No first-order condition is assumed of an arbitrary price.
-- source:
--   Dou & Ji, External Financing and Customer Capital: A Financial Theory of Markups, SSRN 2574953 (version of May 11, 2020), p. 33 (PDF 34), Online Appendix A.1, (A.5)–(A.6)

import Mathlib
import Definitions.Def_FinMarkup_Wedge_Model

namespace FinMarkup.Wedge

/-- Online Appendix A.1, (A.5) and (A.6), p. 33. -/
theorem eq_A5_A6 (m : Params) (hS : m.Standing) (Pt M mu nu p : ℝ)
    (hPt : 0 < Pt) (hM : 0 < M) (hmu : 0 ≤ mu) (hnu : 0 < nu) (hp : 0 < p) :
    mu * (-(m.beta * m.eta * p ^ (-m.eta - 1) * Pt ^ (m.eta - m.eps) * M)) +
      nu * ((p ^ (-m.eta) * Pt ^ (m.eta - m.eps) -
        (p - m.R / m.A) * m.eta * p ^ (-m.eta - 1) * Pt ^ (m.eta - m.eps)) * M) = 0 ↔
    p = m.eta / (m.eta - 1) * (m.R / m.A) -
      m.beta * m.eta / (m.eta - 1) * (mu / nu) := by sorry

end FinMarkup.Wedge
