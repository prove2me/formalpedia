-- Prove2me | Theorems.Thm_CondMat0408017_memory_effect_angle_shift
-- name    : CondMat0408017.memory_effect_angle_shift
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-26T13:25:33.898795+00:00
-- url     : https://prove2.me/theorems/edbb10c9-8c7b-5dc1-922c-58d47db012cc
-- title:
--   Text after eq. (160): under the memory-effect condition a speckle feature moves by $\Delta\theta_s=\Delta\theta_0\cos\theta_0/\cos\theta_s$
-- statement:
--   Let $|\theta_s|<\pi/2$ and $\theta_0$ be real. When the angle of incidence changes from $\theta_0$ to $\theta$, a speckle feature at $\theta_s$ that keeps the momentum transfer fixed, $q'-k'=q-k$ with $k=\sqrt{\varepsilon_0}\frac\omega c\sin\theta_0$ and $q=\sqrt{\varepsilon_0}\frac\omega c\sin\theta_s$, moves to $\theta_s'(\theta)=\arcsin(\sin\theta+\sin\theta_s-\sin\theta_0)$. Then:
--
--   1. $\theta_s'(\theta_0)=\theta_s$.
--   2. For $\theta$ near $\theta_0$, $\sin\theta_s'(\theta)-\sin\theta=\sin\theta_s-\sin\theta_0$, which is the condition $\Delta_{q'k'}=\Delta_{qk}$ divided by $\sqrt{\varepsilon_0}\omega/c$.
--   3. $\theta_s'$ is differentiable at $\theta_0$ with derivative $\cos\theta_0/\cos\theta_s$. So to first order in $\Delta\theta_0$,
--   $$\Delta\theta_s=\Delta\theta_0\,\frac{\cos\theta_0}{\cos\theta_s} .$$
--
--   **Formalization Note** "To first order" is read as the derivative of the shifted angle with respect to the angle of incidence. The common factor $\sqrt{\varepsilon_0}\,\omega/c$ of $k$ and $q$ cancels from the condition. The paper's remark that the shift can be seen in Fig. 22 is not a mathematical statement.
-- source:
--   I. Simonsen, A random walk through surface scattering phenomena: Theory and phenomenology, arXiv:cond-mat/0408017v1 (2004), claim c032; Sec. IV.C.2, text after eq. (PHEN:Eq:C1_condition) [(160)], with eq. (151), PDF p. 55

import Mathlib
import Definitions.Def_CondMat0408017_Basic

open MeasureTheory Filter Topology Complex

namespace CondMat0408017

theorem memory_effect_angle_shift (θ0 θs : ℝ) (hθs : |θs| < Real.pi / 2) :
    memoryShiftAngle θ0 θs θ0 = θs ∧
    (∀ᶠ θ in 𝓝 θ0,
      Real.sin (memoryShiftAngle θ0 θs θ) - Real.sin θ = Real.sin θs - Real.sin θ0) ∧
    HasDerivAt (memoryShiftAngle θ0 θs) (Real.cos θ0 / Real.cos θs) θ0 := by sorry

end CondMat0408017
