-- Prove2me | Theorems.Thm_BenchmarkTracking_Verification_eq_4_7
-- name    : BenchmarkTracking.Verification.eq_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:26:04.657327+00:00
-- url     : https://prove2.me/theorems/0d5f87b2-54da-477d-ba94-9c544757ff62
-- title:
--   Proof of Theorem 4.1, (4.7) — linear growth of the feedback controls $\theta^*$ and $c^*$
-- statement:
--   Let the model parameters satisfy the standing assumptions, with $\mu_Z>\kappa_2$ and $\sigma_B\neq0$. There is $\rho_0>0$, depending only on the model parameters, such that for every discount rate $\rho>\rho_0$ the following holds. On any probability space carrying three independent standard Brownian motions, let $u$ be the function (4.1) and $(\theta^*,c^*)$ the feedback control (4.3) built from it. Then there are constants $C_o>0$ and $C_q>0$ such that for all $(x,h,z)\in\mathbb R^3_+$
--   $$
--   |\theta^*(x,h,z)|\le C_o(1+x+z),\qquad |c^*(x,h,z)|\le C_q(1+x).
--   $$
--
--   These linear-growth bounds make the feedback strategy admissible and drive the moment estimates in the proof of the verification inequality.
--
--   **Formalization Note** $|\cdot|$ on $\mathbb R^d$ is the Euclidean norm. The paper proves (4.7) inside the proof of Theorem 4.1(ii), under $\rho>\rho_0$ with $\rho_0$ of (4.45); that formula depends on $\rho$ itself and on a symbol $\kappa$ not defined in the paper, so the threshold is stated existentially. The explicit constants (4.30), (4.35) are not required.
-- source:
--   Bo, Huang & Yu, Stochastic control problems with state-reflections arising from relaxed benchmark tracking, arXiv:2302.08302v4, p. 20, proof of Theorem 4.1, (4.7)

import Mathlib
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_BenchmarkTracking_Verification_Model
import Definitions.Def_BenchmarkTracking_Verification_Representation
import Definitions.Def_BenchmarkTracking_Verification_Control

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Matrix

namespace BenchmarkTracking.Verification

theorem eq_4_7 {d : ℕ} (M : Params d) (hM : M.Standing) (hZ : M.kappa2 < M.muZ)
    (hσB : M.sigmaB ≠ 0) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, ρ₀ < ρ →
      ∀ (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
        (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin 3)), EthierKurtz.IsStandardBrownian Pr B →
      ∃ Co : ℝ, 0 < Co ∧ ∃ Cq : ℝ, 0 < Cq ∧
        ∀ x h z : ℝ, 0 ≤ x → 0 ≤ h → 0 ≤ z →
          Real.sqrt (thetaStar M (uPrimal M ρ Pr B) x h z ⬝ᵥ
              thetaStar M (uPrimal M ρ Pr B) x h z) ≤ Co * (1 + x + z) ∧
            |cStar M (uPrimal M ρ Pr B) x h z| ≤ Cq * (1 + x) := by sorry

end BenchmarkTracking.Verification
