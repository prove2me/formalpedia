-- Prove2me | Theorems.Thm_ControlledWorldModels_identifiability_state_transition
-- name    : ControlledWorldModels.identifiability_state_transition
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T18:58:15.33204+00:00
-- url     : https://prove2.me/theorems/6d50559d-e0df-4cfa-8d4c-298894ba936e
-- title:
--   Theorem 1: identifiability of state and controlled transition
-- statement:
--   Assume Assumptions 1–2. Let $g:\mathbb{R}^d\to\mathcal X$ be an invertible observation map, measurable with measurable inverse. Let $\mathcal F$ be a class of measurable predictors that realises the optimal conditional-mean predictor $F_h^\star$ of every admissible encoder (Assumption 3). Minimize $\mathcal L_\pi(h,F)$ over measurable encoders $h:\mathcal X\to\mathbb{R}^d$ with $h(x_t)\sim\mathcal N(0,I_d)$ and over $F\in\mathcal F$. Suppose
--
--   $$\gamma_{\rm rep}(\pi)=\lambda_{\min}(R_\pi)-\lambda_{\max}(R_\pi)^2>0\qquad\text{and}\qquad\rho_{\rm tr}(\pi)=\lambda_{\min}(\Sigma_{\rm tr}(\pi))>0.$$
--
--   1. Let $(h,F)$ be a global minimizer whose predictor $F$ is continuous. Then there is $Q\in O(d)$ such that $h(g(z_t))=Qz_t$ almost surely, $F(h(g(z_t)),a_t)=Q(Az_t+Ba_t)$ almost surely, and
--   $$F(y,a)=QAQ^\top y+QBa\qquad\text{for every }(y,a)\in\mathbb{R}^d\times\mathbb{R}^m.$$
--   2. The objective is at least $d-\operatorname{tr}(R_\pi)$ for every admissible encoder and every $F\in\mathcal F$, and $\operatorname{tr}\operatorname{Cov}(\xi_t)=d-\operatorname{tr}(R_\pi)$.
--   3. Conversely, for every $Q\in O(d)$, the encoder $h_Q=Q\,g^{-1}$ is admissible, and with the predictor $F_Q(y,a)=QAQ^\top y+QBa$ it attains $\mathcal L_\pi(h_Q,F_Q)=d-\operatorname{tr}(R_\pi)$.
--
--   Every global minimizer of the action-conditioned predictive objective therefore recovers the latent state and the controlled conditional-mean dynamics up to one common orthogonal transformation.
--
--   **Formalization Note** Assumption 3's sentence "the learned predictor is continuous" is read as continuity of the minimizing predictor $F$, not of every member of $\mathcal F$. A class consisting only of continuous predictors cannot realise every $F_h^\star$ (see the mission report), so that reading would make the theorem vacuous. The minimum value is stated as a lower bound attained by $(h_Q,F_Q)$; $F_Q$ need not belong to $\mathcal F$.
-- source:
--   Zhang, Guan, Zhang, Li, Zhang and Li, On the Identifiability of Controlled World Models, arXiv:2607.22430v2 (2026), Section 3.2, Theorem 1, eqs. (1)-(3), p. 4; Assumptions 1-3, pp. 3-4; proof in Appendix A, p. 9

import Mathlib
import Definitions.Def_ControlledWorldModels_Basic

open MeasureTheory ProbabilityTheory

namespace ControlledWorldModels

theorem identifiability_state_transition {X : Type*} [MeasurableSpace X] {d m : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin m) ℝ)
    (μ : Measure ((Fin d → ℝ) × (Fin m → ℝ))) (ν : Measure (Fin d → ℝ))
    (hpol : IsJointGaussianPolicy μ) (htr : IsStationaryTransition A B μ ν)
    (g : (Fin d → ℝ) ≃ᵐ X)
    (Fc : Set ((Fin d → ℝ) → (Fin m → ℝ) → Fin d → ℝ)) (hFc : IsRichPredictorClass A B μ ν Fc)
    (hrep : 0 < repMargin A B μ) (hexc : 0 < transMargin μ) :
    (∀ (h : X → Fin d → ℝ) (F : (Fin d → ℝ) → (Fin m → ℝ) → Fin d → ℝ),
      Measurable h → IsAdmissible (h ∘ g) → F ∈ Fc →
      (∀ (h' : X → Fin d → ℝ) (F' : (Fin d → ℝ) → (Fin m → ℝ) → Fin d → ℝ),
        Measurable h' → IsAdmissible (h' ∘ g) → F' ∈ Fc →
        loss A B μ ν (h ∘ g) F ≤ loss A B μ ν (h' ∘ g) F') →
      Continuous (Function.uncurry F) →
      ∃ Q : Matrix.orthogonalGroup (Fin d) ℝ,
        (∀ᵐ z ∂(stdGauss d), h (g z) = (Q : Matrix (Fin d) (Fin d) ℝ).mulVec z) ∧
        (∀ᵐ w ∂μ, F (h (g w.1)) w.2 =
          (Q : Matrix (Fin d) (Fin d) ℝ).mulVec (A.mulVec w.1 + B.mulVec w.2)) ∧
        (∀ (y : Fin d → ℝ) (a : Fin m → ℝ), F y a = trueMean A B (Q : Matrix (Fin d) (Fin d) ℝ) y a)) ∧
    (∀ (h' : X → Fin d → ℝ) (F' : (Fin d → ℝ) → (Fin m → ℝ) → Fin d → ℝ),
      Measurable h' → IsAdmissible (h' ∘ g) → F' ∈ Fc →
      ENNReal.ofReal (optValue A B μ) ≤ loss A B μ ν (h' ∘ g) F') ∧
    (covMat ν (fun x => x)).trace = optValue A B μ ∧
    (∀ Q : Matrix.orthogonalGroup (Fin d) ℝ,
      Measurable (fun x => (Q : Matrix (Fin d) (Fin d) ℝ).mulVec (g.symm x)) ∧
      IsAdmissible ((fun x => (Q : Matrix (Fin d) (Fin d) ℝ).mulVec (g.symm x)) ∘ g) ∧
      loss A B μ ν ((fun x => (Q : Matrix (Fin d) (Fin d) ℝ).mulVec (g.symm x)) ∘ g)
        (trueMean A B (Q : Matrix (Fin d) (Fin d) ℝ)) = ENNReal.ofReal (optValue A B μ)) := by sorry

end ControlledWorldModels
