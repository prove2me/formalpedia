-- Prove2me | Theorems.Thm_EndToEndRisk_SquaredLoss_lemma_4
-- name    : EndToEndRisk.SquaredLoss.lemma_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:19:08.216847+00:00
-- url     : https://prove2.me/theorems/481fa802-27d0-4a55-8fc7-18e0963408d9
-- title:
--   Lemma 4, (14), p. 21 — alternative form of δ_ℓ(ϵ;𝒫) indexed by x = x∗(d), x′ = x∗(c̄) and the conditional mean c̄
-- statement:
--   Let $X$, $f$ and the argmin selection $x^*$ be as in the standing setting, let $L$ be the true loss (2), let $\ell$ be any loss, and let $Q$ be a class of integrable probability laws of $c$. Then the calibration function (13) has the alternative form
--   $$\delta_\ell(\epsilon; Q) = \inf_{x, x' \in X}\ \inf_{\substack{d:\, x^*(d) = x \\ \bar c:\, x^*(\bar c) = x'}}\ \inf_{\substack{\nu \in Q \\ \mathbb E_\nu[c] = \bar c}} \Big\{ \mathbb E_\nu[\ell(d,c)] - \min_{d'} \mathbb E_\nu[\ell(d',c)] \;:\; f(x) - f(x') + \bar c^\top (x - x') \ge \epsilon \Big\}. \qquad (14)$$
--
--   The constraint of (13), on the conditional excess true risk, becomes a condition on the decisions $x = x^*(d)$, $x' = x^*(\bar c)$ and the conditional mean $\bar c$ only.
--
--   **Formalization Note** The infimum over "$\mathbb P \in \mathcal P$, $w \in W$ with $\mathbb E[c \mid w] = \bar c$" is the infimum over conditional laws $\nu \in Q$ with mean $\bar c$; infima over empty sets are $+\infty$.
-- source:
--   Ho-Nguyen & Kılınç-Karzan, Risk guarantees for end-to-end prediction and optimization processes, arXiv:2012.15046v1, p. 21, Lemma 4, (14) (proof p. ec9)

import Mathlib
import Definitions.Def_EndToEndRisk_SquaredLoss_Setting

namespace EndToEndRisk.SquaredLoss

open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace

/-- Lemma 4, (14), p. 21 (proof p. ec9): the alternative form of `δ_ℓ(ε; Q)` for the true loss,
indexed by `x = x∗(d)`, `x′ = x∗(c̄)` and the conditional mean `c̄`. -/
theorem lemma_4 {m : ℕ}
    (X : Set (EuclideanSpace ℝ (Fin m))) (f : EuclideanSpace ℝ (Fin m) → ℝ) (hS : Standing X f)
    (xstar : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (hx : IsArgminSelection X f xstar)
    (ℓ : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) → ℝ)
    (Q : Set (Measure (EuclideanSpace ℝ (Fin m))))
    (hQ : ∀ ν ∈ Q, IsProbabilityMeasure ν ∧ Integrable (fun c => c) ν) (ε : ℝ) :
    deltaL ℓ (trueLoss X f xstar) Q ε =
      ⨅ x ∈ X, ⨅ x' ∈ X, ⨅ (d : EuclideanSpace ℝ (Fin m)) (_ : xstar d = x),
        ⨅ (cbar : EuclideanSpace ℝ (Fin m)) (_ : xstar cbar = x'),
          ⨅ ν ∈ Q, ⨅ (_ : (∫ c, c ∂ν) = cbar),
            ⨅ (_ : ε ≤ f x - f x' + ⟪cbar, x - x'⟫_ℝ), condExcess ℓ ν d := by sorry

end EndToEndRisk.SquaredLoss
