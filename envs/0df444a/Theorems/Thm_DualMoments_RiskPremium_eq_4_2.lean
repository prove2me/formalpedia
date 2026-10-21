-- Prove2me | Theorems.Thm_DualMoments_RiskPremium_eq_4_2
-- name    : DualMoments.RiskPremium.eq_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:39:36.716713+00:00
-- url     : https://prove2.me/theorems/6b758390-7a4d-4284-b81c-7052ce3dff35
-- title:
--   (4.2), §4, p. 8 — the RDU risk premium λ is the unique solution of (4.2) with −ε2 < −λ < ε2
-- statement:
--   Let $U$ be twice continuously differentiable with $U' > 0$, let $h$ satisfy the standing assumptions, let $0 < p_0 < 1$, $0 < \varepsilon_1 < \min\{p_0, 1-p_0\}$, $\varepsilon_2 > 0$ and $w_0 \in \mathbb R$.
--
--   1. For every $\lambda \in \mathbb R$: $\lambda$ is an RDU risk premium for the change from $C$ to $D$ (that is, $-\varepsilon_2 < -\lambda < \varepsilon_2$ and the RDU decision-maker is indifferent between $C$ and $D$ with $y = 0 - \lambda$, all outcomes shifted by $w_0$) if and only if $-\varepsilon_2 < -\lambda < \varepsilon_2$ and
--   $$h(p_0)U(w_0 - \varepsilon_2) + (1 - h(p_0))U(w_0 + \varepsilon_2) = h(p_0 - \varepsilon_1)U(w_0 - \varepsilon_2) + \bigl(h(p_0 + \varepsilon_1) - h(p_0 - \varepsilon_1)\bigr)U(w_0 - \lambda) + \bigl(1 - h(p_0 + \varepsilon_1)\bigr)U(w_0 + \varepsilon_2).$$
--   2. There is exactly one RDU risk premium $\lambda$.
--
--   The paper defines $\lambda$ as "the solution to (4.2)"; this statement makes that definite: the indifference equation is (4.2), and it has exactly one solution in the range the page allows.
-- source:
--   Eeckhoudt & Laeven, Dual Moments and Risk Attitudes, arXiv:1612.03347v2, (4.2), §4, p. 8

import Mathlib
import Definitions.Def_DualMoments_RiskPremium_Model

namespace DualMoments.RiskPremium

theorem eq_4_2 (U h : ℝ → ℝ) (hU : UtilityStanding U) (hh : WeightingStanding h)
    (p0 w0 ε₁ ε₂ : ℝ) (hf : Feasible p0 ε₁) (hε₂ : 0 < ε₂) :
    (∀ lam : ℝ, IsRDUPremium U h p0 w0 ε₁ ε₂ lam ↔
      (-ε₂ < -lam ∧ -lam < ε₂ ∧
        h p0 * U (w0 - ε₂) + (1 - h p0) * U (w0 + ε₂) =
          h (p0 - ε₁) * U (w0 - ε₂) + (h (p0 + ε₁) - h (p0 - ε₁)) * U (w0 - lam) +
            (1 - h (p0 + ε₁)) * U (w0 + ε₂))) ∧
    ∃! lam : ℝ, IsRDUPremium U h p0 w0 ε₁ ε₂ lam := by sorry

end DualMoments.RiskPremium
