-- Prove2me | Theorems.Thm_CapScaleML_ABCS_proposition_2_2
-- name    : CapScaleML.ABCS.proposition_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:49:22.669986+00:00
-- url     : https://prove2.me/theorems/0e928e26-01af-482b-9655-15d7431a6888
-- title:
--   Proposition 2.2 — existence of an offline optimal schedule
-- statement:
--   Let $T>0$, $\omega,\beta>0$, $\theta\ge0$, and let $\lambda$ be a nonnegative integrable arrival rate. Among all feasible server schedules, an optimum is attained:
--   $$
--   \exists m^*,q^*\quad \operatorname{Cost}^{\lambda}(m^*,T)=\operatorname{Opt}.
--   $$
--   The attaining schedule supplies the offline component of AP and the comparator used in the performance bounds.
--
--   **Formalization Note** Integrability is explicit. The source assumes finite $\operatorname{Opt}$ without loss of generality; an infinite optimum is attained by any feasible schedule in the extended-real convention.
-- source:
--   Rutten & Mukherjee, Online Capacity Scaling Augmented With Unreliable Machine Learning Predictions, arXiv:2101.12160v2, p. 8, Proposition 2.2

import Mathlib
import Definitions.Def_CapScaleML_ABCS_Defs

open MeasureTheory Set

namespace CapScaleML.ABCS

/-- Proposition 2.2: the offline capacity-scaling optimum is attained. -/
theorem proposition_2_2 (ω β θ T : ℝ) (hω : 0 < ω) (hβ : 0 < β)
    (hθ : 0 ≤ θ) (hT : 0 < T) (lam : ℝ → ℝ)
    (hlam : ∀ t ∈ Icc 0 T, 0 ≤ lam t)
    (hlamI : IntervalIntegrable lam volume 0 T) :
    ∃ m q : ℝ → ℝ, IsOfflineOpt ω β θ T lam m q := by sorry

end CapScaleML.ABCS
