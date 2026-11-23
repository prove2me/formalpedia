-- Prove2me | Theorems.Thm_ControlledWorldModels_exploration_noise_scaling
-- name    : ControlledWorldModels.exploration_noise_scaling
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T19:02:00.395649+00:00
-- url     : https://prove2.me/theorems/9b137fcc-296b-4253-acdd-6cc3a0ec89f3
-- title:
--   Corollary 1: exploration-noise scaling
-- statement:
--   Let $d,m\ge1$, $K\in\mathbb{R}^{m\times d}$ and $\sigma\in[0,1]$. Consider the behavior policy $a_t=\sqrt{1-\sigma^2}\,Kz_t+\sigma\eta_t$ with $z_t\sim\mathcal N(0,I_d)$ and $\eta_t\sim\mathcal N(0,I_m)$ independent, and suppose Assumption 2 holds for this policy (a Gaussian noise $\nu$ making the process stationary). Let $\mathcal F$ satisfy Assumption 3 and, for a fixed $Q\in O(d)$, contain $F^\star(y,a)+D(a-\mu_{\pi_\sigma}(Q^\top y))$ for every $D\in\mathbb{R}^{d\times m}$. Then:
--
--   1. $\Sigma_{\rm tr}(\pi_\sigma)=\sigma^2I_m$ and $\rho_{\rm tr}(\pi_\sigma)=\sigma^2$;
--   2. if $\sigma>0$, then for every $\delta>0$ the class contains a continuous $F_\delta$ with $\mathcal E_{\pi_\sigma}(F_\delta)=\delta$ and $\mathcal E_{\rm cf}(F_\delta)=\delta/\sigma^2$;
--   3. if $\sigma=0$, the class contains a continuous $\widetilde F$ with $\mathcal E_{\pi_0}(\widetilde F)=0$ and $\mathcal E_{\rm cf}(\widetilde F)=1$. (This is the whole of item 3. Outside the statement: taking $D=0$ in the class hypothesis gives $F^\star\in\mathcal F$ with both errors $0$, so two predictors in the class agree on-policy but differ counterfactually. This is the sense in which the transition is not identifiable outside the support of the behavior distribution.)
--
--   **Formalization Note** The paper's informal clause for $\sigma=0$ ("not identifiable outside its support") is formalized as the construction in its proof (Appendix C). The dimensions $d,m\ge1$ are implicit in the paper; they are needed for $\lambda_{\min}$ of an $m\times m$ matrix and for the unit vectors of the construction.
-- source:
--   Zhang, Guan, Zhang, Li, Zhang and Li, On the Identifiability of Controlled World Models, arXiv:2607.22430v2 (2026), Section 3.4, Corollary 1, p. 5; proof in Appendix C, pp. 10-11

import Mathlib
import Definitions.Def_ControlledWorldModels_Basic

open MeasureTheory ProbabilityTheory

namespace ControlledWorldModels

theorem exploration_noise_scaling {d m : ℕ} (hd : 1 ≤ d) (hm : 1 ≤ m)
    (A : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin m) ℝ)
    (K : Matrix (Fin m) (Fin d) ℝ) (σ : ℝ) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (ν : Measure (Fin d → ℝ)) (htr : IsStationaryTransition A B (policyLaw K σ) ν)
    (Fc : Set ((Fin d → ℝ) → (Fin m → ℝ) → Fin d → ℝ))
    (hFc : IsRichPredictorClass A B (policyLaw K σ) ν Fc)
    (Q : Matrix.orthogonalGroup (Fin d) ℝ)
    (hcls : ∀ D : Matrix (Fin d) (Fin m) ℝ,
      (fun y a => trueMean A B (Q : Matrix (Fin d) (Fin d) ℝ) y a +
        D.mulVec (a - condMeanAct (policyLaw K σ)
          ((Q : Matrix (Fin d) (Fin d) ℝ).transpose.mulVec y))) ∈ Fc) :
    condActCov (policyLaw K σ) = σ ^ 2 • (1 : Matrix (Fin m) (Fin m) ℝ) ∧
    transMargin (policyLaw K σ) = σ ^ 2 ∧
    (0 < σ → ∀ δ : ℝ, 0 < δ → ∃ F ∈ Fc, Continuous (Function.uncurry F) ∧
      onPolicyExcess A B (policyLaw K σ) ν (Q : Matrix (Fin d) (Fin d) ℝ) F = ENNReal.ofReal δ ∧
      cfError A B (policyLaw K σ) (Q : Matrix (Fin d) (Fin d) ℝ) F = ENNReal.ofReal (δ / σ ^ 2)) ∧
    (σ = 0 → ∃ F ∈ Fc, Continuous (Function.uncurry F) ∧
      onPolicyExcess A B (policyLaw K σ) ν (Q : Matrix (Fin d) (Fin d) ℝ) F = 0 ∧
      cfError A B (policyLaw K σ) (Q : Matrix (Fin d) (Fin d) ℝ) F = 1) := by sorry

end ControlledWorldModels
