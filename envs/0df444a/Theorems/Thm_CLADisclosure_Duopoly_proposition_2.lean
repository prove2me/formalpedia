-- Prove2me | Theorems.Thm_CLADisclosure_Duopoly_proposition_2
-- name    : CLADisclosure.Duopoly.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:20:46.345984+00:00
-- url     : https://prove2.me/theorems/cad08afd-4397-4f83-adb3-5b6b47d9e5c9
-- title:
--   Proposition 2, p. 18 — loss aversion lowers disclosure threshold and raises ex ante profit
-- statement:
--   Fix a quality distribution with continuous positive density, a strictly increasing $G$, a positive disclosure cost $c$, and a gain sensitivity $g>0$. Compare two loss sensitivities $g\le l_1<l_2$ at the same $g$. Suppose the cost is below $G(1)+(l_1-g)H(1)$ and both corresponding symmetric disclosure thresholds $\hat q_1,\hat q_2$ meet the consumer participation bound. Then
--
--   $$\hat q_2<\hat q_1\qquad\text{and}\qquad E(\pi^d_1)<E(\pi^d_2).$$
--
--   Stronger consumer loss aversion therefore induces more quality disclosure and strictly increases either firm's ex ante profit in this symmetric duopoly.
--
--   **Formalization Note** The game defines each threshold by best response and each ex ante profit from conditional Bertrand profits. The participation hypotheses express footnote 3. The case $l_1=g$, used as a benchmark on p. 12, is included alongside the paper's standing $l>g$ case.
-- source:
--   Zhang & Li, Quality Disclosure under Consumer Loss Aversion, SSRN 3544738 (version of 2020-01-20), p. 18 (PDF 20), Proposition 2(a,b); footnote 3 p. 15 (PDF 17)

import Mathlib
import Definitions.Def_CLADisclosure_Duopoly_Model

open MeasureTheory intervalIntegral

namespace CLADisclosure.Duopoly

/-- Proposition 2(a,b), p. 18: more loss aversion lowers the symmetric threshold and raises profit. -/
theorem proposition_2 {F f : ℝ → ℝ} (hF : QualityDist F f)
    (hG : StrictMonoOn (Gfun F) (Set.Ioc (0 : ℝ) 1))
    {c g l₁ l₂ x₁ x₂ : ℝ} (hc : 0 < c) (hg : 0 < g)
    (hk₁ : g ≤ l₁) (hk : l₁ < l₂)
    (hcost : c < Gfun F 1 + (l₁ - g) * Hfun F 1)
    (h₁ : IsSymEqThreshold F f g l₁ c x₁)
    (h₂ : IsSymEqThreshold F f g l₂ c x₂) :
    x₂ < x₁ ∧ exAnteProfit F f g l₁ c x₁ < exAnteProfit F f g l₂ c x₂ := by sorry

end CLADisclosure.Duopoly
