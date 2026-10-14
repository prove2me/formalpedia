-- Prove2me | Theorems.Thm_BenchmarkTracking_Verification_remark_3_6
-- name    : BenchmarkTracking.Verification.remark_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:26:21.919869+00:00
-- url     : https://prove2.me/theorems/62ff1055-fa9d-46cb-8218-51ab1623d4b3
-- title:
--   Remark 3.6 — $\psi_r+\psi_{rr}>0$ on $\mathbb R^2_+$
-- statement:
--   Let the model parameters satisfy the standing assumptions, let $\rho>0$ and $\sigma_B\neq0$. On any probability space carrying three independent standard Brownian motions, let $\psi=\varphi+\xi$ be the function of Proposition 3.5. Then
--   $$
--   \psi_r(r,h)+\psi_{rr}(r,h)>0\qquad\text{for all }(r,h)\in\mathbb R^2_+ .
--   $$
--
--   Since $\hat u_{yy}=y^{-2}(v_{rr}+v_r)$, this is the input from the last term of $v$ for the strict convexity of $y\mapsto\hat u(y,h,z)$ in Theorem 3.1, and for the bound on $\theta^*$ in the proof of Theorem 4.1.
--
--   **Formalization Note** $\sigma_B\neq0$ is added, as in Proposition 3.5. Derivatives at $r=0$ are one-sided. The representations (3.43)–(3.45) are not part of this statement.
-- source:
--   Bo, Huang & Yu, Stochastic control problems with state-reflections arising from relaxed benchmark tracking, arXiv:2302.08302v4, pp. 17–18, Remark 3.6

import Mathlib
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_BenchmarkTracking_Verification_Model
import Definitions.Def_BenchmarkTracking_Verification_Analysis
import Definitions.Def_BenchmarkTracking_Verification_Representation
import Definitions.Def_BenchmarkTracking_Verification_PDE

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace BenchmarkTracking.Verification

theorem remark_3_6 {d : ℕ} (M : Params d) (hM : M.Standing) (ρ : ℝ) (hρ0 : 0 < ρ)
    (hσB : M.sigmaB ≠ 0)
    {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin 3)) (hB : EthierKurtz.IsStandardBrownian Pr B) :
    ∀ r h : ℝ, 0 ≤ r → 0 ≤ h →
      0 < pd2₁ (psiRep M ρ Pr B) (Ici 0) r h +
        pd2₁ (pd2₁ (psiRep M ρ Pr B) (Ici 0)) (Ici 0) r h := by sorry

end BenchmarkTracking.Verification
