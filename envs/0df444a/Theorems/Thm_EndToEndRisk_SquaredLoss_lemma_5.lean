-- Prove2me | Theorems.Thm_EndToEndRisk_SquaredLoss_lemma_5
-- name    : EndToEndRisk.SquaredLoss.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:19:16.263648+00:00
-- url     : https://prove2.me/theorems/3b408c32-1163-4c00-b255-d14f3094b36f
-- title:
--   Lemma 5, p. 21 — x∗(d) = x, x∗(c̄) = x′ ⇒ ‖d − c̄‖₂ ≥ max{0, f(x) − f(x′) + c̄ᵀ(x − x′)}/‖x − x′‖₂
-- statement:
--   Let $X$, $f$ and the argmin selection $x^*$ be as in the standing setting. Fix distinct $x, x' \in X$, and let $d, \bar c \in \mathbb R^m$ satisfy $x^*(d) = x$ and $x^*(\bar c) = x'$. Then
--   $$\|d - \bar c\|_2 \ \ge\ \frac{\max\{0,\ f(x) - f(x') + \bar c^\top (x - x')\}}{\|x - x'\|_2}.$$
--
--   A prediction $d$ whose decision is far from optimal under the cost $\bar c$ must itself be far from $\bar c$; this is the geometric input to the lower bound on the calibration function of the squared loss (Theorem 4).
-- source:
--   Ho-Nguyen & Kılınç-Karzan, Risk guarantees for end-to-end prediction and optimization processes, arXiv:2012.15046v1, p. 21, Lemma 5 (proof p. ec10)

import Mathlib
import Definitions.Def_EndToEndRisk_SquaredLoss_Setting

namespace EndToEndRisk.SquaredLoss

open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace

/-- Lemma 5, p. 21 (proof p. ec10): for distinct `x, x′ ∈ X` with `x∗(d) = x` and
`x∗(c̄) = x′`, `‖d − c̄‖₂ ≥ max{0, f(x) − f(x′) + c̄ᵀ(x − x′)} / ‖x − x′‖₂`. -/
theorem lemma_5 {m : ℕ}
    (X : Set (EuclideanSpace ℝ (Fin m))) (f : EuclideanSpace ℝ (Fin m) → ℝ) (hS : Standing X f)
    (xstar : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (hx : IsArgminSelection X f xstar)
    (x x' : EuclideanSpace ℝ (Fin m)) (hxX : x ∈ X) (hx'X : x' ∈ X) (hne : x ≠ x')
    (d cbar : EuclideanSpace ℝ (Fin m)) (hd : xstar d = x) (hc : xstar cbar = x') :
    max 0 (f x - f x' + ⟪cbar, x - x'⟫_ℝ) / ‖x - x'‖ ≤ ‖d - cbar‖ := by sorry

end EndToEndRisk.SquaredLoss
