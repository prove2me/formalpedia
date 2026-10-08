-- Prove2me | Theorems.Thm_AddLogReg_ExpCrit_lemma_1
-- name    : AddLogReg.ExpCrit.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T23:04:46.90833+00:00
-- url     : https://prove2.me/theorems/aaf6023b-c488-4876-abdd-285b1d285104
-- title:
--   Lemma 1, p. 345 — E(e^{−yF(x)}) is minimized at F(x) = ½ log[P(y=1|x)/P(y=−1|x)]; hence (13)–(14)
-- statement:
--   Let $X$ be a measurable space of features and $\nu$ a probability measure on $X \times \{-1, 1\}$, the joint law of the feature $x$ and the label $y$; let $\nu_X$ be its marginal on $X$ and $P(y = \pm 1 \mid x)$ the conditional class probabilities. Assume that $0 < P(y = 1 \mid x) < 1$ for $\nu_X$-almost every $x$. Let
--   $$F^\star(x) = \tfrac12 \log \frac{P(y = 1 \mid x)}{P(y = -1 \mid x)} \qquad (12).$$
--   Then
--
--   1. $F^\star$ is measurable;
--   2. $F^\star$ minimizes the exponential criterion $J(F) = E(e^{-yF(x)})$: for every measurable $F : X \to \mathbb R$,
--   $$E\big(e^{-yF^\star(x)}\big) \le E\big(e^{-yF(x)}\big);$$
--   3. for $\nu_X$-almost every $x$, (13) and (14) hold at $F^\star$:
--   $$P(y = 1 \mid x) = \frac{e^{F^\star(x)}}{e^{-F^\star(x)} + e^{F^\star(x)}}, \qquad P(y = -1 \mid x) = \frac{e^{-F^\star(x)}}{e^{-F^\star(x)} + e^{F^\star(x)}}.$$
--
--   Lemma 1 is the basis of the paper's statistical view of boosting: the population minimizer of the exponential criterion that AdaBoost optimizes is half the log-odds, so the additive model AdaBoost builds is an additive logistic regression model, and its fitted values can be turned into class probabilities by the symmetric logistic transform.
--
--   **Formalization Note** The expectation is under the joint law, as a lower Lebesgue integral in $[0, \infty]$, so competitors with $E(e^{-yF(x)}) = \infty$ are included and honestly beaten. The assumption $0 < P(y = 1 \mid x) < 1$ almost everywhere is a disclosed addition: where a class probability is $0$ the ratio in (12) is $0$ or undefined, `Real.log` would return the junk value $0$, and no minimizer of $J$ exists if the assumption fails on a set of positive measure. The conditional probabilities come from Mathlib's conditional kernel of $\nu$ and are determined only almost everywhere, hence item 3 holds almost everywhere. Uniqueness of the minimizer is not claimed.
-- source:
--   Friedman, Hastie and Tibshirani, Additive logistic regression: a statistical view of boosting, Ann. Statist. 28 (2000), p. 345, Lemma 1, (12)–(14)

import Mathlib
import Definitions.Def_AddLogReg_ExpCrit_Setting

open MeasureTheory ProbabilityTheory

namespace AddLogReg.ExpCrit

/-- Lemma 1 (p. 345): `E(e^{−yF(x)})` is minimized at `F(x) = ½ log [P(y = 1|x)/P(y = −1|x)]`
(12), over all measurable `F`; hence (13) and (14) hold at that `F`. -/
theorem lemma_1 {X : Type*} [MeasurableSpace X] (ν : Measure (X × Bool)) [IsProbabilityMeasure ν]
    (hη : ∀ᵐ x ∂ν.fst, 0 < condProb ν true x ∧ condProb ν true x < 1) :
    Measurable (halfLogit ν) ∧
    (∀ F : X → ℝ, Measurable F → J ν (halfLogit ν) ≤ J ν F) ∧
    (∀ᵐ x ∂ν.fst,
      condProb ν true x = Real.exp (halfLogit ν x) /
          (Real.exp (-halfLogit ν x) + Real.exp (halfLogit ν x)) ∧
      condProb ν false x = Real.exp (-halfLogit ν x) /
          (Real.exp (-halfLogit ν x) + Real.exp (halfLogit ν x))) := by sorry

end AddLogReg.ExpCrit
