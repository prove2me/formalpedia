-- Prove2me | Theorems.Thm_EndToEndRisk_SquaredLoss_lemma_3
-- name    : EndToEndRisk.SquaredLoss.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:19:10.218863+00:00
-- url     : https://prove2.me/theorems/12524bd3-c761-4d62-b893-88e009693e39
-- title:
--   Lemma 3, p. 20 — ℓ is 𝒫-uniformly calibrated if and only if δ_ℓ(ϵ;𝒫) > 0 for all ϵ > 0
-- statement:
--   Let $\ell$ be a surrogate loss and $L$ the target loss on $\mathbb R^m \times \mathbb R^m$, and let $Q$ be a class of conditional laws of $c$. Then $\ell$ is $Q$-uniformly calibrated (Definition 5) if and only if its calibration function (13) is positive away from zero:
--   $$\ell \text{ is } Q\text{-uniformly calibrated} \iff \delta_\ell(\epsilon; Q) > 0 \ \text{ for all } \epsilon > 0.$$
--
--   This reduces uniform calibration to a lower bound on a single function of $\epsilon$, which is how uniform calibration of the squared loss is proved (Theorem 4).
--
--   **Formalization Note** The statement holds for an arbitrary pair of losses, so $L$ is a parameter; the paper applies it with $L$ the true loss (2). The class is a set of conditional laws (see the definitions file).
-- source:
--   Ho-Nguyen & Kılınç-Karzan, Risk guarantees for end-to-end prediction and optimization processes, arXiv:2012.15046v1, p. 20, Lemma 3 (proof pp. ec8–ec9)

import Mathlib
import Definitions.Def_EndToEndRisk_SquaredLoss_Setting

namespace EndToEndRisk.SquaredLoss

open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace

/-- Lemma 3, p. 20 (proof pp. ec8–ec9): a surrogate loss `ℓ` is `Q`-uniformly calibrated (with
respect to the loss `L`) if and only if `δ_ℓ(ε; Q) > 0` for every `ε > 0`. -/
theorem lemma_3 {m : ℕ}
    (ℓ L : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) → ℝ)
    (Q : Set (Measure (EuclideanSpace ℝ (Fin m)))) :
    UniformlyCalibrated ℓ L Q ↔ ∀ ε : ℝ, 0 < ε → 0 < deltaL ℓ L Q ε := by sorry

end EndToEndRisk.SquaredLoss
