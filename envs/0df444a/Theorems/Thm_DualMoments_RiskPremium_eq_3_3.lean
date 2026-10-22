-- Prove2me | Theorems.Thm_DualMoments_RiskPremium_eq_3_3
-- name    : DualMoments.RiskPremium.eq_3_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T12:39:41.998984+00:00
-- url     : https://prove2.me/theorems/532d9f5b-54e9-4e67-af1c-c0120a7d3dc0
-- title:
--   (3.3), §3, p. 6 — the explicit solution for the DT risk premium ρ
-- statement:
--   Under the standing assumptions on $h$, $p_0$ and $\varepsilon_1$ (as in (3.2)), and for every initial wealth $w_0$, a number $\rho$ is a DT risk premium for the change from $A$ to $B$ if and only if
--   $$\rho = \frac{\bigl(h(p_0) - h(p_0 - \varepsilon_1)\bigr) - \bigl(h(p_0 + \varepsilon_1) - h(p_0)\bigr)}{h(p_0 + \varepsilon_1) - h(p_0 - \varepsilon_1)}.$$
--
--   In particular the DT risk premium exists, is unique, and does not depend on $w_0$. The forward direction is the paper's explicit solution (3.3); the converse states that this value lies in $(-1, 1)$ and solves (3.2), so the approximation (3.4) is not about an empty set of premia.
-- source:
--   Eeckhoudt & Laeven, Dual Moments and Risk Attitudes, arXiv:1612.03347v2, (3.3), §3, p. 6

import Mathlib
import Definitions.Def_DualMoments_RiskPremium_Model

namespace DualMoments.RiskPremium

theorem eq_3_3 (h : ℝ → ℝ) (hh : WeightingStanding h) (p0 w0 ε₁ ρ : ℝ) (hf : Feasible p0 ε₁) :
    IsDTPremium h p0 w0 ε₁ ρ ↔
      ρ = ((h p0 - h (p0 - ε₁)) - (h (p0 + ε₁) - h p0)) / (h (p0 + ε₁) - h (p0 - ε₁)) := by sorry

end DualMoments.RiskPremium
