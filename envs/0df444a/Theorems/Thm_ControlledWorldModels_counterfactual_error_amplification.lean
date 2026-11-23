-- Prove2me | Theorems.Thm_ControlledWorldModels_counterfactual_error_amplification
-- name    : ControlledWorldModels.counterfactual_error_amplification
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T19:01:21.22801+00:00
-- url     : https://prove2.me/theorems/f66900f0-f489-4274-b398-5b52ef2a4eeb
-- title:
--   Theorem 3: counterfactual error amplification
-- statement:
--   Assume Assumptions 1–3 with $\gamma_{\rm rep}(\pi)>0$ and $\rho_{\rm tr}(\pi)>0$. Fix identified coordinates $y=Qz$, $Q\in O(d)$, and let $F^\star(y,a)=QAQ^\top y+QBa$ and $\mu_\pi(z)=\mathbb E_\pi[a_t\mid z_t=z]$. Suppose the predictor class $\mathcal F$ contains
--   $$F^\star(y,a)+D\big(a-\mu_\pi(Q^\top y)\big)$$
--   for every matrix $D\in\mathbb{R}^{d\times m}$. Then for every $\delta>0$ the class contains a continuous predictor $F_\delta$ with
--
--   $$\mathcal E_\pi(F_\delta)=\delta,\qquad\mathcal E_{\rm cf}(F_\delta)=\frac{\delta}{\rho_{\rm tr}(\pi)}.$$
--
--   A small on-policy excess risk is therefore compatible with a counterfactual error larger by the factor $1/\rho_{\rm tr}(\pi)$.
--
--   **Formalization Note** $\mu_\pi$ is the linear version $z\mapsto\mathbb E[a_tz_t^\top]z$ of the conditional mean, as used in the paper's proof. The statement holds for every $Q\in O(d)$. It therefore generalizes the paper's statement, which concerns the $Q$ identified by a minimizer; it is not merely equivalent to it.
-- source:
--   Zhang, Guan, Zhang, Li, Zhang and Li, On the Identifiability of Controlled World Models, arXiv:2607.22430v2 (2026), Section 3.4, Theorem 3, eqs. (5)-(6), p. 5; proof in Appendix C, p. 10

import Mathlib
import Definitions.Def_ControlledWorldModels_Basic

open MeasureTheory ProbabilityTheory

namespace ControlledWorldModels

theorem counterfactual_error_amplification {d m : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin m) ℝ)
    (μ : Measure ((Fin d → ℝ) × (Fin m → ℝ))) (ν : Measure (Fin d → ℝ))
    (hpol : IsJointGaussianPolicy μ) (htr : IsStationaryTransition A B μ ν)
    (Fc : Set ((Fin d → ℝ) → (Fin m → ℝ) → Fin d → ℝ)) (hFc : IsRichPredictorClass A B μ ν Fc)
    (hrep : 0 < repMargin A B μ) (hexc : 0 < transMargin μ)
    (Q : Matrix.orthogonalGroup (Fin d) ℝ)
    (hcls : ∀ D : Matrix (Fin d) (Fin m) ℝ,
      (fun y a => trueMean A B (Q : Matrix (Fin d) (Fin d) ℝ) y a +
        D.mulVec (a - condMeanAct μ ((Q : Matrix (Fin d) (Fin d) ℝ).transpose.mulVec y))) ∈ Fc)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ F ∈ Fc, Continuous (Function.uncurry F) ∧
      onPolicyExcess A B μ ν (Q : Matrix (Fin d) (Fin d) ℝ) F = ENNReal.ofReal δ ∧
      cfError A B μ (Q : Matrix (Fin d) (Fin d) ℝ) F = ENNReal.ofReal (δ / transMargin μ) := by sorry

end ControlledWorldModels
