-- Prove2me | Theorems.Thm_CLADisclosure_Duopoly_eq_7
-- name    : CLADisclosure.Duopoly.eq_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:20:54.462296+00:00
-- url     : https://prove2.me/theorems/39f62e20-54f6-4560-ba9f-53b095f675d3
-- title:
--   Equation (7), p. 18 — ex ante profit as a nested CDF integral
-- statement:
--   Let $0<\hat q\le1$ solve the symmetric threshold equation for positive gain sensitivity $g$, positive disclosure cost $c$, and nonnegative $k=l-g$. Assume also that the undisclosed product has nonnegative expected gross utility. For every disclosed quality $q_a\in[\hat q,1]$, the firm's conditional profit simplifies to
--
--   $$\pi_a^c(q_a)=\int_{\hat q}^{q_a}F(q_b)\,dq_b.$$
--
--   The resulting ex ante profit of either firm is
--
--   $$E(\pi^d)=\int_{\hat q}^{1}\int_{\hat q}^{q_a}F(q_b)\,dq_b\,dF(q_a).$$
--
--   The second identity is equation (7); it isolates the threshold as the channel through which loss aversion changes ex ante profit.
-- source:
--   Zhang & Li, Quality Disclosure under Consumer Loss Aversion, SSRN 3544738 (version of 2020-01-20), p. A7 (PDF 50), proof of Proposition 2; p. 18 (PDF 20), eq. (7)

import Mathlib
import Definitions.Def_CLADisclosure_Duopoly_Model

open MeasureTheory intervalIntegral

namespace CLADisclosure.Duopoly

/-- The disclosure-profit simplification and equation (7), p. A7 and p. 18. -/
theorem eq_7 {F f : ℝ → ℝ} (hF : QualityDist F f)
    {g l c qh : ℝ} (hc : 0 < c) (hg : 0 < g) (hk : g ≤ l)
    (hqh : qh ∈ Set.Ioc (0 : ℝ) 1)
    (hp : 0 ≤ nondiscUtility F f g l qh)
    (heq : F qh * (Gfun F qh + (l - g) * Hfun F qh) = c) :
    (∀ qa ∈ Set.Icc qh 1,
      discProfit F f g l c qh qa = ∫ qb in qh..qa, F qb) ∧
    exAnteProfit F f g l c qh = Lfun F f qh := by sorry

end CLADisclosure.Duopoly
