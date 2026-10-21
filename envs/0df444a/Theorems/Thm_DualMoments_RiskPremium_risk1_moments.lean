-- Prove2me | Theorems.Thm_DualMoments_RiskPremium_risk1_moments
-- name    : DualMoments.RiskPremium.risk1_moments
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:39:32.134312+00:00
-- url     : https://prove2.me/theorems/d908b2f6-0ea0-40f4-bcbd-2c4a48580e8d
-- title:
--   §3, p. 6 — for the risk ε̃1, unconditionally m̄2 = 2ε1² and Pr = 2ε1
-- statement:
--   Let $\varepsilon_1 \in \mathbb R$ and let $\tilde\varepsilon_1$ be the sub-probability risk taking the values $-1$ and $+1$, each with unconditional probability $\varepsilon_1$. Its unconditional maxiance $\bar m_2 = \int (x - m)\,\mathrm d(F(x))^2$ and its total unconditional mass $\Pr$ are
--   $$\bar m_2 = 2\varepsilon_1^2, \qquad \Pr = 2\varepsilon_1.$$
--
--   The risk $\tilde\varepsilon_1$ describes the mean-preserving spread from lottery $B$ with $x = 0$ to lottery $A$. These values identify the leading coefficient $\bar m_2/(2\Pr) = \varepsilon_1/2$ in the DT risk-premium approximation (3.4).
-- source:
--   Eeckhoudt & Laeven, Dual Moments and Risk Attitudes, arXiv:1612.03347v2, §3, p. 6, 'One readily verifies that, for this risk ε̃1, we have that, unconditionally, m̄2 = 2ε1² and Pr = 2ε1.'

import Mathlib
import Definitions.Def_DualMoments_RiskPremium_Model

namespace DualMoments.RiskPremium

theorem risk1_moments (ε₁ : ℝ) :
    (risk1 ε₁).maxiance = 2 * ε₁ ^ 2 ∧ (risk1 ε₁).mass = 2 * ε₁ := by sorry

end DualMoments.RiskPremium
