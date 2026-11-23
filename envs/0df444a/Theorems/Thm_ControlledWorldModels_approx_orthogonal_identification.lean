-- Prove2me | Theorems.Thm_ControlledWorldModels_approx_orthogonal_identification
-- name    : ControlledWorldModels.approx_orthogonal_identification
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T18:59:57.226523+00:00
-- url     : https://prove2.me/theorems/8bdf1809-3ea7-41e5-b56a-d4ce1e4d11a4
-- title:
--   Lemma 4: approximate orthogonal identification
-- statement:
--   There is a universal constant $C>0$ with the following property. Assume Assumptions 1–2 (in any dimensions $d,m$) and $\gamma_{\rm rep}(\pi)>0$. Let $h$ be an admissible encoder with $\mathcal L_\pi(h,F_h^\star)\le d-\operatorname{tr}R_\pi+\Delta$ for some $\Delta\ge0$. Then there exists $Q\in O(d)$ with
--
--   $$\mathbb E\|h(g(z_t))-Qz_t\|^2\le C\,\frac{\Delta}{\gamma_{\rm rep}(\pi)}.$$
--
--   **Formalization Note** "Universal constant" is read as a single $C$ chosen before $d$, $m$, the dynamics, the policy and the encoder.
-- source:
--   Zhang, Guan, Zhang, Li, Zhang and Li, On the Identifiability of Controlled World Models, arXiv:2607.22430v2 (2026), Appendix B, Lemma 4, p. 10 (setting: Section 3.3, Theorem 2, p. 4)

import Mathlib
import Definitions.Def_ControlledWorldModels_Basic

open MeasureTheory ProbabilityTheory

namespace ControlledWorldModels

theorem approx_orthogonal_identification :
    ∃ C : ℝ, 0 < C ∧
    ∀ {d m : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin m) ℝ)
      (μ : Measure ((Fin d → ℝ) × (Fin m → ℝ))) (ν : Measure (Fin d → ℝ)),
      IsJointGaussianPolicy μ → IsStationaryTransition A B μ ν →
      ∀ e : (Fin d → ℝ) → Fin d → ℝ, IsAdmissible e → 0 < repMargin A B μ →
      ∀ Δ : ℝ, 0 ≤ Δ →
      condLoss A B μ ν e ≤ ENNReal.ofReal (optValue A B μ) + ENNReal.ofReal Δ →
      ∃ Q : Matrix.orthogonalGroup (Fin d) ℝ,
        ∫⁻ z, ENNReal.ofReal (sqNorm (e z - (Q : Matrix (Fin d) (Fin d) ℝ).mulVec z)) ∂(stdGauss d) ≤
          ENNReal.ofReal (C * (Δ / repMargin A B μ)) := by sorry

end ControlledWorldModels
