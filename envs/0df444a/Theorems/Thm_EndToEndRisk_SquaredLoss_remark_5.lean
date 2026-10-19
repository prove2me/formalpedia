-- Prove2me | Theorems.Thm_EndToEndRisk_SquaredLoss_remark_5
-- name    : EndToEndRisk.SquaredLoss.remark_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:19:29.934795+00:00
-- url     : https://prove2.me/theorems/0b3122ba-dd9b-4f33-b8f2-bbbb3ce7c2a0
-- title:
--   Remark 5, p. 19 — the conditional excess true risk is f(x∗(d)) − f(x∗(c̄)) + c̄ᵀ(x∗(d) − x∗(c̄)) ≤ B_f + B_C B_X
-- statement:
--   Let $X$, $f$ and the argmin selection $x^*$ be as in the standing setting, let $C \subset \mathbb R^m$ be bounded (Assumption 2), and let $\nu$ be an integrable probability law of $c$ whose mean $\bar c = \mathbb E_\nu[c]$ lies in $\mathrm{Conv}(C)$ (the role of $\mathbb P[\cdot \mid w]$). For every $d \in \mathbb R^m$, the conditional excess true risk satisfies
--   $$\begin{aligned}\mathbb E_\nu[L(d,c)] - \min_{d'} \mathbb E_\nu[L(d',c)] &= f(x^*(d)) - f(x^*(\bar c)) + \bar c^\top\big(x^*(d) - x^*(\bar c)\big) \\ &\le f(x^*(d)) - f(x^*(\bar c)) + \|\bar c\|_2\, \|x^*(d) - x^*(\bar c)\|_2 \\ &\le B_f + B_C B_X,\end{aligned}$$
--   where $B_f$, $B_C$, $B_X$ are the constants (11).
--
--   The bound makes the conditional excess true risk uniformly bounded, which is the hypothesis under which the calibration function can be convexified on a bounded interval in Theorem 3.
--
--   **Formalization Note** Both sides are compared in $[0,\infty]$ via $\mathrm{ofReal}$; $B_X$ is `Metric.diam X`, which equals the maximum for compact $X$.
-- source:
--   Ho-Nguyen & Kılınç-Karzan, Risk guarantees for end-to-end prediction and optimization processes, arXiv:2012.15046v1, p. 19, Remark 5 (with the first display of the proof of Lemma 4, p. ec9)

import Mathlib
import Definitions.Def_EndToEndRisk_SquaredLoss_Setting

namespace EndToEndRisk.SquaredLoss

open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace

/-- Remark 5, p. 19: for a conditional law `ν` with mean `c̄ ∈ Conv(C)`, the conditional excess
true risk of `d` is `f(x∗(d)) − f(x∗(c̄)) + c̄ᵀ(x∗(d) − x∗(c̄))`, which is at most
`f(x∗(d)) − f(x∗(c̄)) + ‖c̄‖₂ ‖x∗(d) − x∗(c̄)‖₂ ≤ B_f + B_C B_X`. -/
theorem remark_5 {m : ℕ}
    (X : Set (EuclideanSpace ℝ (Fin m))) (f : EuclideanSpace ℝ (Fin m) → ℝ) (hS : Standing X f)
    (xstar : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (hx : IsArgminSelection X f xstar)
    (C : Set (EuclideanSpace ℝ (Fin m))) (hA2 : Bornology.IsBounded C)
    (ν : Measure (EuclideanSpace ℝ (Fin m))) [IsProbabilityMeasure ν]
    (hC : ν Cᶜ = 0) (hint : Integrable (fun c => c) ν)
    (hmean : (∫ c, c ∂ν) ∈ convexHull ℝ C)
    (d : EuclideanSpace ℝ (Fin m)) :
    condExcess (trueLoss X f xstar) ν d =
        ENNReal.ofReal (f (xstar d) - f (xstar (∫ c, c ∂ν)) +
          ⟪∫ c, c ∂ν, xstar d - xstar (∫ c, c ∂ν)⟫_ℝ) ∧
      condExcess (trueLoss X f xstar) ν d ≤
        ENNReal.ofReal (f (xstar d) - f (xstar (∫ c, c ∂ν)) +
          ‖∫ c, c ∂ν‖ * ‖xstar d - xstar (∫ c, c ∂ν)‖) ∧
      condExcess (trueLoss X f xstar) ν d ≤
        ENNReal.ofReal (Bf X f + Bc C * Metric.diam X) := by sorry

end EndToEndRisk.SquaredLoss
