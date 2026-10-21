-- Prove2me | Theorems.Thm_EndToEndRisk_SquaredLoss_lemma_2
-- name    : EndToEndRisk.SquaredLoss.lemma_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:19:18.287558+00:00
-- url     : https://prove2.me/theorems/b99e4e72-1b62-4c57-b5e3-e945679704df
-- title:
--   Lemma 2, p. 10 — the conditional mean g∗(w) = E[c | w] minimizes the true risk, and R(ℙ) = E[min_{d′} E[L(d′,c) | w]]
-- statement:
--   Let $X$, $f$ and the argmin selection $x^*$ be as in the standing setting, with $x^*$ measurable. Let $(w,c)$ have joint law $\mathbb P$ on $W \times \mathbb R^m$, with $w \sim \mu$ and conditional law $\mathbb P[\cdot \mid w]$ integrable for every $w$. Write $L$ for the true loss (2), $R(g,\mathbb P) = \mathbb E[L(g(w),c)]$ and $R(\mathbb P) = \inf_g\{R(g,\mathbb P) : g \text{ measurable}\}$. Then:
--
--   1. the conditional mean $g^*(w) := \mathbb E[c \mid w]$ is a measurable function of $w$;
--   2. $g^*$ attains the Bayes risk: $R(g^*,\mathbb P) = R(\mathbb P)$;
--   3. the Bayes risk is the average of the pointwise conditional minima:
--   $$R(\mathbb P) = \mathbb E\Big[ \min_{d' \in \mathbb R^m} \mathbb E[L(d',c) \mid w] \Big].$$
--
--   The lemma identifies the best possible end-to-end predictor as the regression function, which is what makes regression-type surrogate losses natural for this problem.
--
--   **Formalization Note** The joint law is $\mu \otimes \kappa$ for a probability measure $\mu$ and a Markov kernel $\kappa$; $\mathbb E[c \mid w]$ is the Bochner integral $\int c \, d\kappa(w)$, and the minimum over $d'$ is written as an infimum. Measurability of $x^*$ is added: the paper works with Lebesgue measurability (Lemma EC.4), and a Borel-measurable selection always exists (Lemma EC.2).
-- source:
--   Ho-Nguyen & Kılınç-Karzan, Risk guarantees for end-to-end prediction and optimization processes, arXiv:2012.15046v1, p. 10, Lemma 2 (proof p. ec3)

import Mathlib
import Definitions.Def_EndToEndRisk_SquaredLoss_Setting

namespace EndToEndRisk.SquaredLoss

open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace

/-- Lemma 2, p. 10 (proof p. ec3): the conditional mean `g∗(w) = E[c | w]` is measurable and
minimizes the true risk over measurable predictors, and `R(ℙ) = E[min_{d′} E[L(d′, c) | w]]`. -/
theorem lemma_2 {m : ℕ} {W : Type*} [MeasurableSpace W]
    (X : Set (EuclideanSpace ℝ (Fin m))) (f : EuclideanSpace ℝ (Fin m) → ℝ) (hS : Standing X f)
    (xstar : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (hx : IsArgminSelection X f xstar) (hxm : Measurable xstar)
    (μ : Measure W) [IsProbabilityMeasure μ]
    (κ : Kernel W (EuclideanSpace ℝ (Fin m))) [IsMarkovKernel κ]
    (hint : ∀ w, Integrable (fun c => c) (κ w)) :
    Measurable (fun w => ∫ c, c ∂(κ w)) ∧
      risk (trueLoss X f xstar) (μ ⊗ₘ κ) (fun w => ∫ c, c ∂(κ w)) =
        bayesRisk (trueLoss X f xstar) (μ ⊗ₘ κ) ∧
      bayesRisk (trueLoss X f xstar) (μ ⊗ₘ κ) =
        ∫⁻ w, ⨅ d', condRisk (trueLoss X f xstar) (κ w) d' ∂μ := by sorry

end EndToEndRisk.SquaredLoss
