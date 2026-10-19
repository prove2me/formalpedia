-- Prove2me | Theorems.Thm_CLADisclosure_Duopoly_profits_formula
-- name    : CLADisclosure.Duopoly.profits_formula
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:20:43.806842+00:00
-- url     : https://prove2.me/theorems/0a1c5dc3-2bbc-41fc-80e8-53b5cd635ae1
-- title:
--   p. 14 — nondisclosure and disclosure profit formulas
-- statement:
--   Let $g>0$, $0<\hat q\le1$, $k=l-g\ge0$, and suppose consumers value the undisclosed product at a nonnegative amount. Against a rival that discloses precisely when its quality exceeds $\hat q$, a firm concealing its quality earns $\pi_a^n=0$. If it discloses quality $q_a\in[\hat q,1]$, it earns
--
--   $$\pi_a^c(q_a)=\int_0^{\hat q}\bigl[q_a-\bar q+kH(\hat q)\bigr]f(q_b)\,dq_b+\int_{\hat q}^{q_a}(q_a-q_b)f(q_b)\,dq_b-c.$$
--
--   These are the conditional profits used to characterize a symmetric disclosure threshold and compute ex ante profit.
-- source:
--   Zhang & Li, Quality Disclosure under Consumer Loss Aversion, SSRN 3544738 (version of 2020-01-20), p. 14 (PDF 16), §3.3, nondisclosure and disclosure profits

import Mathlib
import Definitions.Def_CLADisclosure_Duopoly_Model

open MeasureTheory intervalIntegral

namespace CLADisclosure.Duopoly

/-- The nondisclosure and disclosure profit formulas on p. 14. -/
theorem profits_formula {F f : ℝ → ℝ} (hF : QualityDist F f)
    {g l c qh : ℝ} (hg : 0 < g) (hk : g ≤ l)
    (hqh : qh ∈ Set.Ioc (0 : ℝ) 1)
    (hp : 0 ≤ nondiscUtility F f g l qh) :
    nondiscProfit F f g l qh = 0 ∧
    (∀ qa ∈ Set.Icc qh 1,
      discProfit F f g l c qh qa =
        (∫ qb in (0 : ℝ)..qh,
          (qa - condMean F f qh + (l - g) * Hfun F qh) * f qb) +
        (∫ qb in qh..qa, (qa - qb) * f qb) - c) := by sorry

end CLADisclosure.Duopoly
