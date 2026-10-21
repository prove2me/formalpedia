-- Prove2me | Theorems.Thm_CapScaleML_ABCS_equation_A_32
-- name    : CapScaleML.ABCS.equation_A_32
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:49:25.847853+00:00
-- url     : https://prove2.me/theorems/cc4fa78c-f57c-44d1-8dcd-2c787d12d2aa
-- title:
--   Equation (A.32) — cost split for AP
-- statement:
--   Write AP's server schedule as $m=m_1+m_2$, where $m_2$ is the online correction and $m_1$ is a feasible schedule for the predicted arrival rate $\tilde\lambda$. Put $\Delta\lambda=(\lambda-\tilde\lambda)^+$. For their respective workloads,
--   $$
--   \operatorname{Cost}^{\lambda}(m,T)\leq
--   \operatorname{Cost}^{\tilde\lambda}(m_1,T)+
--   \operatorname{Cost}^{\Delta\lambda}(m_2,T).
--   $$
--   This separates the forecast-driven capacity from the correction for underprediction.
--
--   **Formalization Note** The result is stated for any feasible $m_1$, as the paper also uses it for an optimizer under the opposite arrival rate. Each workload equation carries integrability.
-- source:
--   Rutten & Mukherjee, Online Capacity Scaling Augmented With Unreliable Machine Learning Predictions, arXiv:2101.12160v2, p. 35, proof of Theorem 4.7, (A.32)

import Mathlib
import Definitions.Def_CapScaleML_ABCS_Defs

open MeasureTheory Set

namespace CapScaleML.ABCS

/-- Equation (A.32), subadditivity of AP's cost decomposition. -/
theorem equation_A_32 (ω β θ T : ℝ) (hω : 0 < ω) (hβ : 0 < β)
    (hθ : 0 ≤ θ) (hT : 0 < T) (lam lamHat m₁ q₁ q₂ q : ℝ → ℝ)
    (hlam : ∀ t ∈ Icc 0 T, 0 ≤ lam t)
    (hlamHat : ∀ t ∈ Icc 0 T, 0 ≤ lamHat t)
    (hlamI : IntervalIntegrable lam volume 0 T)
    (hlamHatI : IntervalIntegrable lamHat volume 0 T)
    (hm₁ : Admissible T m₁) (hq₁ : IsWorkload T lamHat m₁ q₁)
    (hq₂ : IsWorkload T (deltaLam lam lamHat) (apOnline ω β lam lamHat) q₂)
    (hq : IsWorkload T lam (fun t => m₁ t + apOnline ω β lam lamHat t) q) :
    cost ω β θ T (fun t => m₁ t + apOnline ω β lam lamHat t) q ≤
      cost ω β θ T m₁ q₁ + cost ω β θ T (apOnline ω β lam lamHat) q₂ := by sorry

end CapScaleML.ABCS
