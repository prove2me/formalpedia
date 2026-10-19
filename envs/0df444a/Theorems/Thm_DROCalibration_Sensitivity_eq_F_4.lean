-- Prove2me | Theorems.Thm_DROCalibration_Sensitivity_eq_F_4
-- name    : DROCalibration.Sensitivity.eq_F_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:28:19.007976+00:00
-- url     : https://prove2.me/theorems/e961f182-2cd2-4af9-b11b-c062c7b0c4df
-- title:
--   (F.4), p. 48 — [φ′]⁻¹ is continuously differentiable near 0 with [φ′]⁻¹(ζ) = 1 + ζ/φ″(1) + o(ζ)
-- statement:
--   Let $\phi$ satisfy Assumption 2.1. Then the derivative $\phi'$ has a local inverse near $\zeta=0$: there are $\varepsilon,r>0$ and a function $z:(-\varepsilon,\varepsilon)\to(1-r,1+r)$ such that
--
--   1. for every $\zeta\in(-\varepsilon,\varepsilon)$, $z(\zeta)$ is the unique point $y\in(1-r,1+r)$ with $\phi'(y)=\zeta$;
--   2. $z$ is continuously differentiable on $(-\varepsilon,\varepsilon)$, with
--   $$z'(\zeta)=\frac{1}{\phi''(z(\zeta))};$$
--   3. $z(0)=1$ and $z'(0)=1/\phi''(1)$, that is,
--   $$[\phi']^{-1}(\zeta)=1+\frac{\zeta}{\phi''(1)}+o(\zeta)\qquad(\zeta\to0).$$
--
--   This is the inverse-function step of the proof of Proposition F.1: the inner minimization of the Lagrangian is solved by $q_i=p_i[\phi']^{-1}(\delta(-f_i-c))$, and the expansion is what produces the factor $1/\phi''(1)$ in Theorem 2.2.
--
--   **Formalization Note** The paper prints $\phi^{-1}$ and $\phi''(0)$ in (F.4); the surrounding sentence defines $z(\zeta)$ as the solution of $\phi'(z(\zeta))=\zeta$, so the inverse is $[\phi']^{-1}$ and the slope is $1/\phi''(z(0))=1/\phi''(1)$, which is what is stated. The uniqueness clause pins $z$ to the local inverse; $\phi'$, $\phi''$ are derivatives of the real part of $\phi$.
-- source:
--   Gotoh, Kim & Lim, Calibration of Distributionally Robust Empirical Optimization Models, arXiv:1711.06565v2, p. 48, Appendix F, proof of Proposition F.1, (F.4)

import Mathlib
import Definitions.Def_DROCalibration_Sensitivity_Setting

open Filter Topology

namespace DROCalibration.Sensitivity

theorem eq_F_4 (φ : ℝ → EReal) (hφ : Assumption21 φ) :
    ∃ ε > 0, ∃ r > 0, ∃ z : ℝ → ℝ,
      ContDiffOn ℝ 1 z (Set.Ioo (-ε) ε) ∧
      (∀ ζ ∈ Set.Ioo (-ε) ε, z ζ ∈ Set.Ioo (1 - r) (1 + r) ∧ deriv (phiReal φ) (z ζ) = ζ ∧
        ∀ y ∈ Set.Ioo (1 - r) (1 + r), deriv (phiReal φ) y = ζ → y = z ζ) ∧
      (∀ ζ ∈ Set.Ioo (-ε) ε, HasDerivAt z (deriv (deriv (phiReal φ)) (z ζ))⁻¹ ζ) ∧
      z 0 = 1 ∧ HasDerivAt z (phiPP φ)⁻¹ 0 := by sorry

end DROCalibration.Sensitivity
