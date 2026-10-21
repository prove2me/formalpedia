-- Prove2me | Theorems.Thm_DualMoments_RiskPremium_eq_3_2
-- name    : DualMoments.RiskPremium.eq_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:39:28.607324+00:00
-- url     : https://prove2.me/theorems/3b718350-2320-4582-bd54-2408a40c8807
-- title:
--   (3.2), §3, p. 6 — indifference between A and B is equation (3.2)
-- statement:
--   Let $h$ be a probability weighting function satisfying the standing assumptions ($C^2$ on $[0,1]$, $h(0) = 0$, $h(1) = 1$, $h' > 0$), let $0 < p_0 < 1$ and $0 < \varepsilon_1 < \min\{p_0, 1 - p_0\}$, and let $w_0, \rho \in \mathbb R$. Then $\rho$ is a DT risk premium for the change from $A$ to $B$ (that is, $-1 < -\rho < 1$ and the DT decision-maker is indifferent between $A$ and $B$ with $x = 0 - \rho$, all outcomes shifted by the initial wealth $w_0$) if and only if $-1 < -\rho < 1$ and
--   $$h(p_0)(w_0 - 1) + (1 - h(p_0))(w_0 + 1) = h(p_0 - \varepsilon_1)(w_0 - 1) + \bigl(h(p_0 + \varepsilon_1) - h(p_0 - \varepsilon_1)\bigr)(w_0 - \rho) + \bigl(1 - h(p_0 + \varepsilon_1)\bigr)(w_0 + 1).$$
--
--   This unfolds the DT evaluation (3.1) of the lotteries $A$ and $B$ into the explicit equation from which the paper solves for $\rho$.
-- source:
--   Eeckhoudt & Laeven, Dual Moments and Risk Attitudes, arXiv:1612.03347v2, (3.2), §3, p. 6

import Mathlib
import Definitions.Def_DualMoments_RiskPremium_Model

namespace DualMoments.RiskPremium

theorem eq_3_2 (h : ℝ → ℝ) (hh : WeightingStanding h) (p0 w0 ε₁ ρ : ℝ) (hf : Feasible p0 ε₁) :
    IsDTPremium h p0 w0 ε₁ ρ ↔
      (-1 < -ρ ∧ -ρ < 1 ∧
        h p0 * (w0 - 1) + (1 - h p0) * (w0 + 1) =
          h (p0 - ε₁) * (w0 - 1) + (h (p0 + ε₁) - h (p0 - ε₁)) * (w0 - ρ) +
            (1 - h (p0 + ε₁)) * (w0 + 1)) := by sorry

end DualMoments.RiskPremium
