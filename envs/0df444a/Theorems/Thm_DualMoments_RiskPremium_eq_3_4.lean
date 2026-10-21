-- Prove2me | Theorems.Thm_DualMoments_RiskPremium_eq_3_4
-- name    : DualMoments.RiskPremium.eq_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:39:33.549639+00:00
-- url     : https://prove2.me/theorems/51620da2-9c79-4670-8b7c-59544bb55974
-- title:
--   (3.4), §3, p. 6 — the DT risk premium is m̄2/(2Pr)·(−h″(p0)/h′(p0)) up to o(m̄2/Pr) as ε1 → 0⁺
-- statement:
--   Let $h$ satisfy the standing assumptions, let $0 < p_0 < 1$ and $w_0 \in \mathbb R$, and let $\rho(\varepsilon_1)$ be, for every feasible $\varepsilon_1 \in (0, \min\{p_0, 1-p_0\})$, a DT risk premium for the change from $A$ to $B$. Let $\bar m_2(\varepsilon_1)$ and $\Pr(\varepsilon_1)$ be the unconditional maxiance and total mass of the risk $\tilde\varepsilon_1$ ($\pm1$, each with probability $\varepsilon_1$). Then, as $\varepsilon_1 \to 0^+$,
--   $$\rho(\varepsilon_1) = \frac{\bar m_2}{2\Pr}\left(-\frac{h''(p_0)}{h'(p_0)}\right) + o\!\left(\frac{\bar m_2}{\Pr}\right).$$
--
--   This is the paper's local index of absolute risk aversion under Yaari's dual theory: the risk premium of a small risk is proportional to its maxiance, as the Pratt–Arrow premium under expected utility is proportional to the variance.
--
--   **Formalization Note** The paper writes "$\rho \simeq$" for an approximation by second-order Taylor expansions of $h(p_0 \pm \varepsilon_1)$. It is read here as a little-o statement as $\varepsilon_1 \to 0^+$, with remainder small relative to $\bar m_2/\Pr = \varepsilon_1$, the size of the leading term. The maxiance and mass are computed from the risk $\tilde\varepsilon_1$, not hard-coded; $\Pr = 2\varepsilon_1 > 0$ on the filter, so no division by zero occurs there. $h'(p_0)$ and $h''(p_0)$ are ordinary derivatives at the interior point $p_0$.
-- source:
--   Eeckhoudt & Laeven, Dual Moments and Risk Attitudes, arXiv:1612.03347v2, (3.4), §3, p. 6

import Mathlib
import Definitions.Def_DualMoments_RiskPremium_Model

namespace DualMoments.RiskPremium

open Filter Asymptotics Topology in
theorem eq_3_4 (h : ℝ → ℝ) (hh : WeightingStanding h) (p0 w0 : ℝ) (hp0 : 0 < p0 ∧ p0 < 1)
    (ρ : ℝ → ℝ) (hρ : ∀ ε₁, Feasible p0 ε₁ → IsDTPremium h p0 w0 ε₁ (ρ ε₁)) :
    (fun ε₁ : ℝ => ρ ε₁ -
        (risk1 ε₁).maxiance / (2 * (risk1 ε₁).mass) * (-(deriv (deriv h) p0) / deriv h p0))
      =o[𝓝[>] (0 : ℝ)] (fun ε₁ : ℝ => (risk1 ε₁).maxiance / (risk1 ε₁).mass) := by sorry

end DualMoments.RiskPremium
