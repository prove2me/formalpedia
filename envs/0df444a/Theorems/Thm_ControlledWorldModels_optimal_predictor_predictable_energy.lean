-- Prove2me | Theorems.Thm_ControlledWorldModels_optimal_predictor_predictable_energy
-- name    : ControlledWorldModels.optimal_predictor_predictable_energy
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T18:56:58.881452+00:00
-- url     : https://prove2.me/theorems/308a5956-bc20-4c34-8238-224134fa0f10
-- title:
--   Lemma 1: optimal predictor and predictable energy
-- statement:
--   Assume Assumptions 1–2. Let $h$ be an admissible encoder, i.e. $h(x_t)\sim\mathcal N(0,I_d)$. Then:
--
--   1. the optimal predictor for squared loss is the conditional mean $F_h^\star(h(x_t),a_t)=\mathbb E[h(x_{t+1})\mid h(x_t),a_t]$. That is, there is a measurable $F_h^\star:\mathbb{R}^d\times\mathbb{R}^m\to\mathbb{R}^d$ realising this conditional expectation almost surely, and $\mathcal L_\pi(h,F_h^\star)\le\mathcal L_\pi(h,F)$ for every measurable predictor $F$;
--   2. $\mathbb E\|h(x_{t+1})\|^2=d$;
--   3. with $J(h)=\mathbb E\|\mathbb E[h(x_{t+1})\mid h(x_t),a_t]\|^2\le d$,
--   $$\inf_F\mathcal L_\pi(h,F)=d-J(h),$$
--   the infimum being over measurable predictors.
--
--   Minimizing the prediction loss over $F$ is therefore equivalent to maximizing the predictable energy $J(h)$.
--
--   **Formalization Note** The inequality $J(h)\le d$ is stated so that the subtraction in $[0,\infty]$ is the ordinary one. The paper's identity $\inf_F\mathcal L=\mathbb E\|h(x_{t+1})\|^2-J(h)$ appears as items 2 and 3 together.
-- source:
--   Zhang, Guan, Zhang, Li, Zhang and Li, On the Identifiability of Controlled World Models, arXiv:2607.22430v2 (2026), Appendix A, Lemma 1, p. 9 (setting: Section 3.1, Assumptions 1-2, eq. (1), pp. 3-4)

import Mathlib
import Definitions.Def_ControlledWorldModels_Basic

open MeasureTheory ProbabilityTheory

namespace ControlledWorldModels

theorem optimal_predictor_predictable_energy {d m : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin m) ℝ)
    (μ : Measure ((Fin d → ℝ) × (Fin m → ℝ))) (ν : Measure (Fin d → ℝ))
    (hpol : IsJointGaussianPolicy μ) (htr : IsStationaryTransition A B μ ν)
    (e : (Fin d → ℝ) → Fin d → ℝ) (he : IsAdmissible e) :
    (∃ Fstar : (Fin d → ℝ) → (Fin m → ℝ) → Fin d → ℝ, Measurable (Function.uncurry Fstar) ∧
      (fun ω : Sample d m => Fstar (e ω.1.1) ω.1.2) =ᵐ[μ.prod ν] condPred A B μ ν e ∧
      ∀ F : (Fin d → ℝ) → (Fin m → ℝ) → Fin d → ℝ, Measurable (Function.uncurry F) →
        loss A B μ ν e Fstar ≤ loss A B μ ν e F) ∧
    ∫⁻ ω, ENNReal.ofReal (sqNorm (e (nextState A B ω))) ∂(μ.prod ν) = ENNReal.ofReal d ∧
    predEnergy A B μ ν e ≤ ENNReal.ofReal d ∧
    (⨅ (F : (Fin d → ℝ) → (Fin m → ℝ) → Fin d → ℝ) (_ : Measurable (Function.uncurry F)),
        loss A B μ ν e F) = ENNReal.ofReal d - predEnergy A B μ ν e := by sorry

end ControlledWorldModels
