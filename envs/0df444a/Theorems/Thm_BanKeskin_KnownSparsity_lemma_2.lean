-- Prove2me | Theorems.Thm_BanKeskin_KnownSparsity_lemma_2
-- name    : BanKeskin.KnownSparsity.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:02:23.257979+00:00
-- url     : https://prove2.me/theorems/c58e2710-c4da-4b7a-8342-26184d4b722d
-- title:
--   Lemma 2, p. 5556 — high-probability estimation error
-- statement:
--   Under the known-support linear model and ILSX policy, there are finite positive constants $\kappa_2,\rho_2$ and a finite positive threshold $t_0$ such that, for every $\theta_{\mathcal S}\in\Theta_{\mathcal S}$ and $t\ge t_0$,
--
--   $$\mathbb P^{\pi}_{X,\theta_{\mathcal S}}\!\left\{\left\|\widetilde{\mathcal J}_{\mathcal S,t}^{-1}\mathcal M_{\mathcal S,t}\right\|_2^2\le\frac{\rho_2s\log t}{\sqrt t}\right\}\ge 1-\frac{\kappa_2s\log t}{\sqrt t}.$$
--
--   The bound controls the least-squares estimation error on sufficiently late periods and is the immediate statistical input to the regret theorem.
--
--   **Formalization Note** The event also requires $\widetilde{\mathcal J}_{\mathcal S,t}$ to be invertible, since Lean gives the inverse of a singular matrix a default value. The squared Euclidean norm is an explicit coordinate sum. The witness threshold is taken at least two, which can always be achieved by increasing a positive threshold.
-- source:
--   Ban and Keskin, Personalized Dynamic Pricing with Machine Learning, Management Science 67(9) (2021), p. 5556, Lemma 2 and (16); corrected nonsingular-event reading

import Mathlib
import Definitions.Def_BanKeskin_KnownSparsity_Model

open MeasureTheory
open scoped ENNReal

namespace BanKeskin.KnownSparsity

/-- Lemma 2, p. 5556, with nonsingularity included in the probability event. -/
theorem lemma_2 {d : ℕ} {S : Finset (Fin (d + 1))} {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M : Model d S Ω P) (N : NoiseConditions P M) (I : InteriorConditions M)
    (hest : M.IsEstimator) :
    ∃ κ₂ ρ₂ : ℝ, 0 < κ₂ ∧ 0 < ρ₂ ∧
      ∃ t₀ : ℕ, 2 ≤ t₀ ∧
        ∀ θ ∈ M.Theta, ∀ t : ℕ, t₀ ≤ t →
          ENNReal.ofReal (1 - κ₂ * (S.card : ℝ) * Real.log (t : ℝ) /
            Real.sqrt (t : ℝ)) ≤
            P {ω | IsUnit (M.Jtilde t ω).det ∧
              sqNorm (Matrix.mulVec ((M.Jtilde t ω)⁻¹) (M.Mvec t ω)) ≤
                ρ₂ * (S.card : ℝ) * Real.log (t : ℝ) / Real.sqrt (t : ℝ)} := by sorry

end BanKeskin.KnownSparsity
