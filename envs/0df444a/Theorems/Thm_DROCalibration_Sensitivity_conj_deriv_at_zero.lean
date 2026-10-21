-- Prove2me | Theorems.Thm_DROCalibration_Sensitivity_conj_deriv_at_zero
-- name    : DROCalibration.Sensitivity.conj_deriv_at_zero
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T17:28:21.85799+00:00
-- url     : https://prove2.me/theorems/333c0b46-812f-4ed1-9665-6848bb02496a
-- title:
--   Appendix F, p. 49, after (F.6) — φ* is C² near 0 with [φ*]′(0) = 1 and [φ*]″(0) = 1/φ″(1)
-- statement:
--   Let $\phi$ satisfy Assumption 2.1 and let $\phi^*(\zeta)=\sup_z\{\zeta z-\phi(z)\}$ be its convex conjugate (F.5). Then there is $\varepsilon>0$ such that, on $(-\varepsilon,\varepsilon)$:
--
--   1. $\phi^*$ is finite;
--   2. $\phi^*$ is twice continuously differentiable;
--   3. $[\phi^*]'(\zeta)$ solves $\phi'([\phi^*]'(\zeta))=\zeta$, i.e. $[\phi^*]'=[\phi']^{-1}$, and
--   $$[\phi^*]''(\zeta)=\frac{1}{\phi''\big([\phi^*]'(\zeta)\big)};$$
--   4. at $\zeta=0$,
--   $$[\phi^*]'(0)=1,\qquad [\phi^*]''(0)=\frac{1}{\phi''(1)}.$$
--
--   These derivatives enter the first-order condition (F.7) for the multiplier $c^\star(\delta)$ of the dual problem (F.2), and the value $[\phi^*]''(0)=1/\phi''(1)$ is the constant of the worst-case sensitivity.
--
--   **Formalization Note** The paper prints $[\phi^*]''(0)=1/\phi''(0)$; since $[\phi^*]'(0)=1$, the correct value is $1/\phi''(1)$, which is stated. The printed Taylor display $\phi^*(\zeta)=\zeta+\zeta^2/\phi''(0)+o(\zeta^2)$, which also lacks a factor $1/2$, is not stated. Derivatives are those of the real parts of $\phi$ and $\phi^*$; finiteness of $\phi^*$ (neither $+\infty$ nor $-\infty$) is part of the conclusion, so the real part is the conjugate itself.
-- source:
--   Gotoh, Kim & Lim, Calibration of Distributionally Robust Empirical Optimization Models, arXiv:1711.06565v2, pp. 48–49, Appendix F, proof of Proposition F.1, after (F.6)

import Mathlib
import Definitions.Def_DROCalibration_Sensitivity_Setting

open Filter Topology

namespace DROCalibration.Sensitivity

theorem conj_deriv_at_zero (φ : ℝ → EReal) (hφ : Assumption21 φ) :
    ∃ ε > 0,
      (∀ ζ ∈ Set.Ioo (-ε) ε, conj φ ζ ≠ ⊤ ∧ conj φ ζ ≠ ⊥) ∧
      ContDiffOn ℝ 2 (conjReal φ) (Set.Ioo (-ε) ε) ∧
      (∀ ζ ∈ Set.Ioo (-ε) ε, deriv (phiReal φ) (deriv (conjReal φ) ζ) = ζ ∧
        deriv (deriv (conjReal φ)) ζ = (deriv (deriv (phiReal φ)) (deriv (conjReal φ) ζ))⁻¹) ∧
      deriv (conjReal φ) 0 = 1 ∧ deriv (deriv (conjReal φ)) 0 = (phiPP φ)⁻¹ := by sorry

end DROCalibration.Sensitivity
