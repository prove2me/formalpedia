-- Prove2me | Theorems.Thm_EndToEndRisk_SquaredLoss_lemma_6
-- name    : EndToEndRisk.SquaredLoss.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:19:15.067985+00:00
-- url     : https://prove2.me/theorems/22e199c9-0774-4fd4-bbef-9c96c048e949
-- title:
--   Lemma 6, p. 22 — δ_{ℓ_LS}(ϵ;𝒫) = inf ‖d − c̄‖₂² over x∗(d) = x, c̄ ∈ Conv(C), x∗(c̄) = x′, f(x) − f(x′) + c̄ᵀ(x − x′) ≥ ϵ
-- statement:
--   Let $X$, $f$ and the argmin selection $x^*$ be as in the standing setting, let $C \subset \mathbb R^m$ be bounded as in Assumption 2, and let $\mathcal P$ be the class of square-integrable conditional laws of $c$ concentrated on $C$ whose mean lies in $\mathrm{Conv}(C)$ (p. 21). For the squared loss $\ell_{LS}(d,c) = \|d - c\|_2^2$ and every $\epsilon \in \mathbb R$,
--   $$\delta_{\ell_{LS}}(\epsilon; \mathcal P) = \inf_{x, x' \in X}\ \inf_{\substack{d \in \mathbb R^m:\, x^*(d) = x \\ \bar c \in \mathrm{Conv}(C):\, x^*(\bar c) = x'}} \Big\{ \|d - \bar c\|_2^2 \;:\; f(x) - f(x') + \bar c^\top (x - x') \ge \epsilon \Big\}.$$
--
--   By the bias–variance decomposition, the calibration function of the squared loss is a purely geometric quantity, with no probability left in it.
--
--   **Formalization Note** The left side is the calibration function (13) computed from the conditional excess risks of $\ell_{LS}$ and $L$ as defined generically (not from a closed form). Infima over empty sets are $+\infty$.
-- source:
--   Ho-Nguyen & Kılınç-Karzan, Risk guarantees for end-to-end prediction and optimization processes, arXiv:2012.15046v1, p. 22, Lemma 6 (proof p. ec10)

import Mathlib
import Definitions.Def_EndToEndRisk_SquaredLoss_Setting

namespace EndToEndRisk.SquaredLoss

open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace

/-- Lemma 6, p. 22 (proof p. ec10): for the squared loss and the class `𝒫` of square-integrable
conditional laws with mean in `Conv(C)`, `δ_{ℓ_LS}(ε; 𝒫)` is the purely geometric quantity
`inf {‖d − c̄‖₂² : x∗(d) = x, c̄ ∈ Conv(C), x∗(c̄) = x′, f(x) − f(x′) + c̄ᵀ(x − x′) ≥ ε}`. -/
theorem lemma_6 {m : ℕ}
    (X : Set (EuclideanSpace ℝ (Fin m))) (f : EuclideanSpace ℝ (Fin m) → ℝ) (hS : Standing X f)
    (xstar : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (hx : IsArgminSelection X f xstar)
    (C : Set (EuclideanSpace ℝ (Fin m))) (hA2 : Bornology.IsBounded C) (ε : ℝ) :
    deltaL lsLoss (trueLoss X f xstar) (lsClass C) ε =
      ⨅ x ∈ X, ⨅ x' ∈ X, ⨅ (d : EuclideanSpace ℝ (Fin m)) (_ : xstar d = x),
        ⨅ cbar ∈ convexHull ℝ C, ⨅ (_ : xstar cbar = x'),
          ⨅ (_ : ε ≤ f x - f x' + ⟪cbar, x - x'⟫_ℝ), ENNReal.ofReal (‖d - cbar‖ ^ 2) := by sorry

end EndToEndRisk.SquaredLoss
