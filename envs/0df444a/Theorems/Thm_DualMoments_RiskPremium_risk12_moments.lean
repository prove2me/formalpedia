-- Prove2me | Theorems.Thm_DualMoments_RiskPremium_risk12_moments
-- name    : DualMoments.RiskPremium.risk12_moments
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:39:31.817592+00:00
-- url     : https://prove2.me/theorems/c494f046-c045-49a9-b3b3-ccdfadd88cc3
-- title:
--   Footnote 21, p. 8 — for ε̃12, unconditionally m2 = 2ε1ε2², m̄2 = 2ε1²ε2 and Pr = 2ε1
-- statement:
--   Let $\varepsilon_1, \varepsilon_2 \in \mathbb R$ and let $\tilde\varepsilon_{12}$ be the sub-probability risk taking the values $-\varepsilon_2$ and $+\varepsilon_2$, each with unconditional probability $\varepsilon_1$. Its unconditional variance $m_2$, unconditional maxiance $\bar m_2$ and total unconditional mass $\Pr$ are
--   $$m_2 = 2\varepsilon_1\varepsilon_2^2, \qquad \bar m_2 = 2\varepsilon_1^2\varepsilon_2, \qquad \Pr = 2\varepsilon_1.$$
--
--   The risk $\tilde\varepsilon_{12}$ dictates the mean-preserving spread from lottery $D$ with $y = 0$ to lottery $C$. These values turn the two leading terms of the RDU approximation (4.3) into $\tfrac{\varepsilon_2^2}{2}\bigl(-U''(w_0)/U'(w_0)\bigr)$ and $\tfrac{\varepsilon_1\varepsilon_2}{2}\bigl(-h''(p_0)/h'(p_0)\bigr)$.
-- source:
--   Eeckhoudt & Laeven, Dual Moments and Risk Attitudes, arXiv:1612.03347v2, footnote 21, p. 8

import Mathlib
import Definitions.Def_DualMoments_RiskPremium_Model

namespace DualMoments.RiskPremium

theorem risk12_moments (ε₁ ε₂ : ℝ) :
    (risk12 ε₁ ε₂).variance = 2 * ε₁ * ε₂ ^ 2 ∧ (risk12 ε₁ ε₂).maxiance = 2 * ε₁ ^ 2 * ε₂ ∧
      (risk12 ε₁ ε₂).mass = 2 * ε₁ := by sorry

end DualMoments.RiskPremium
