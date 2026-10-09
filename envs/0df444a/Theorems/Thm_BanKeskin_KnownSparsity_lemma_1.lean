-- Prove2me | Theorems.Thm_BanKeskin_KnownSparsity_lemma_1
-- name    : BanKeskin.KnownSparsity.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:02:25.81704+00:00
-- url     : https://prove2.me/theorems/febcd708-1e52-45da-ab5b-8cf7398b1509
-- title:
--   Lemma 1, p. 5556 — information-matrix minimum eigenvalue
-- statement:
--   Under the known-support linear model and ILSX policy, there are finite positive constants $\gamma_1,\kappa_1,\rho_1$ such that, for every $\theta_{\mathcal S}\in\Theta_{\mathcal S}$ and $t\ge2$,
--
--   $$\mathbb P^{\pi}_{X,\theta_{\mathcal S}}\!\left\{\mu_{\min}(\widetilde{\mathcal J}_{\mathcal S,t})\ge\gamma_1J_t\right\}\ge 1-\kappa_1s\exp(-\rho_1J_t).$$
--
--   Here $s=|\mathcal S|$, $J_t$ is experimental price variation, and $\widetilde{\mathcal J}_{\mathcal S,t}$ is the experimental information matrix. This is the high-probability information guarantee used to control estimation error.
--
--   **Formalization Note** The minimum-eigenvalue inequality is expressed as its equivalent Rayleigh bound for every vector. The event depends only on features, so its probability is the same for every parameter. The lower probability bound is truncated at zero when negative, as is automatic for any probability inequality.
-- source:
--   Ban and Keskin, Personalized Dynamic Pricing with Machine Learning, Management Science 67(9) (2021), p. 5556, Lemma 1 and (14)

import Mathlib
import Definitions.Def_BanKeskin_KnownSparsity_Model

open MeasureTheory
open scoped ENNReal

namespace BanKeskin.KnownSparsity

/-- Lemma 1, p. 5556, with the minimum eigenvalue expressed by a Rayleigh bound. -/
theorem lemma_1 {d : ℕ} {S : Finset (Fin (d + 1))} {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M : Model d S Ω P) (N : NoiseConditions P M) (I : InteriorConditions M)
    (hest : M.IsEstimator) :
    ∃ γ₁ κ₁ ρ₁ : ℝ, 0 < γ₁ ∧ 0 < κ₁ ∧ 0 < ρ₁ ∧
      ∀ θ ∈ M.Theta, ∀ t : ℕ, 2 ≤ t →
        ENNReal.ofReal (1 - κ₁ * (S.card : ℝ) * Real.exp (-ρ₁ * M.J t)) ≤
          P {ω | ∀ v : Parameter d S,
            γ₁ * M.J t * sqNorm v ≤ dot v (Matrix.mulVec (M.Jtilde t ω) v)} := by sorry

end BanKeskin.KnownSparsity
