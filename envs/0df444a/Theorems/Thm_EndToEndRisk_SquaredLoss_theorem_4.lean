-- Prove2me | Theorems.Thm_EndToEndRisk_SquaredLoss_theorem_4
-- name    : EndToEndRisk.SquaredLoss.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:19:18.278778+00:00
-- url     : https://prove2.me/theorems/21ea2c4d-587f-45bc-8781-fa3c3138e274
-- title:
--   Theorem 4, p. 22 — the squared loss is 𝒫-uniformly calibrated, with δ_{ℓ_LS}(ϵ;𝒫) ≥ ϵ²/B_X² > 0
-- statement:
--   Let $X$, $f$ and the argmin selection $x^*$ be as in the standing setting, suppose $B_X = \operatorname{diam}(X) > 0$, let $C \subset \mathbb R^m$ be bounded as in Assumption 2, and let $\mathcal P$ be the class of square-integrable conditional laws concentrated on $C$ with mean in $\mathrm{Conv}(C)$. The squared loss $\ell_{LS}$ is $\mathcal P$-uniformly calibrated with respect to the true loss $L$, and its calibration function satisfies
--   $$\delta_{\ell_{LS}}(\epsilon; \mathcal P) \ \ge\ \frac{\epsilon^2}{B_X^2} \ >\ 0 \qquad \text{for all } \epsilon > 0,$$
--   where $B_X$ is the Euclidean diameter of $X$.
--
--   This is the uniform-calibration input to the risk bound of Corollary 3, and the bound is independent of $f$, of $C$ and of the law of the data.
--
--   **Formalization Note** $B_X$ is `Metric.diam X`. The explicit $B_X > 0$ keeps the printed positive quotient meaningful; the paper leaves this denominator condition implicit.
-- source:
--   Ho-Nguyen & Kılınç-Karzan, Risk guarantees for end-to-end prediction and optimization processes, arXiv:2012.15046v1, p. 22, Theorem 4 (proof p. ec10)

import Mathlib
import Definitions.Def_EndToEndRisk_SquaredLoss_Setting

namespace EndToEndRisk.SquaredLoss

open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace

/-- Theorem 4, p. 22 (proof p. ec10): the squared loss is `𝒫`-uniformly calibrated, with
`δ_{ℓ_LS}(ε; 𝒫) ≥ ε² / B_X² > 0` for every `ε > 0`. -/
theorem theorem_4 {m : ℕ}
    (X : Set (EuclideanSpace ℝ (Fin m))) (f : EuclideanSpace ℝ (Fin m) → ℝ) (hS : Standing X f)
    (xstar : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (hx : IsArgminSelection X f xstar)
    (C : Set (EuclideanSpace ℝ (Fin m))) (hA2 : Bornology.IsBounded C)
    (hBX : 0 < Metric.diam X) :
    UniformlyCalibrated lsLoss (trueLoss X f xstar) (lsClass C) ∧
      ∀ ε : ℝ, 0 < ε →
        ENNReal.ofReal (ε ^ 2 / Metric.diam X ^ 2) ≤
            deltaL lsLoss (trueLoss X f xstar) (lsClass C) ε ∧
          0 < deltaL lsLoss (trueLoss X f xstar) (lsClass C) ε := by sorry

end EndToEndRisk.SquaredLoss
