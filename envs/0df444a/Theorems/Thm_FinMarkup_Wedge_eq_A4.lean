-- Prove2me | Theorems.Thm_FinMarkup_Wedge_eq_A4
-- name    : FinMarkup.Wedge.eq_A4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T20:38:38.615212+00:00
-- url     : https://prove2.me/theorems/f9ef3006-5f00-46a8-9d05-6f08519ce3af
-- title:
--   Appendix (A.4) — derivative of expected cash growth
-- statement:
--   Let $P>0$ be the firm's price, $P_t>0$ the industry price index, $M$ its customer base, $W$ its cash balance, and $R/A$ its marginal production cost. The derivative of the expected cash drift with respect to the firm's price is
--
--   $$\frac{\partial g_W}{\partial P}(P)=\left[P^{-\eta}P_t^{\eta-\epsilon}-(P-R/A)\eta P^{-\eta-1}P_t^{\eta-\epsilon}\right]M.$$
--
--   This supplies the liquidity term in the pricing first-order condition.
--
--   **Formalization Note** $g_W$ is the expected drift per unit time in the liquidity-hoarding region, so $dt$ is omitted. The statement carries the model's standing conditions $1<\epsilon<\eta$, $\beta\ge0$, $A,R>0$, and $M>0$. The price-independent cash carrying term remains in $g_W$ but differentiates to zero.
-- source:
--   Dou & Ji, External Financing and Customer Capital: A Financial Theory of Markups, SSRN 2574953 (version of May 11, 2020), p. 33 (PDF 34), Online Appendix A.1, (A.4)

import Mathlib
import Definitions.Def_FinMarkup_Wedge_Model

namespace FinMarkup.Wedge

/-- Online Appendix A.1, (A.4), p. 33. -/
theorem eq_A4 (m : Params) (hS : m.Standing) (Pt M W p : ℝ)
    (hPt : 0 < Pt) (hM : 0 < M) (hp : 0 < p) :
    HasDerivAt (fun q => driftW m Pt M W q)
      ((p ^ (-m.eta) * Pt ^ (m.eta - m.eps) -
        (p - m.R / m.A) * m.eta * p ^ (-m.eta - 1) * Pt ^ (m.eta - m.eps)) * M) p := by sorry

end FinMarkup.Wedge
