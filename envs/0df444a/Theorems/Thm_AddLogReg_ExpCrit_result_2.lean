-- Prove2me | Theorems.Thm_AddLogReg_ExpCrit_result_2
-- name    : AddLogReg.ExpCrit.result_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T23:04:47.94183+00:00
-- url     : https://prove2.me/theorems/40674f84-2c31-47c5-b2e4-98736a9a8390
-- title:
--   Result 2 with (23)–(24), pp. 348–349 — the Real AdaBoost step f = ½ log(P_w(y=1|x)/P_w(y=−1|x)) minimizes J(F + f), and F + f is the minimizer (12)
-- statement:
--   Let $\nu$ be the joint law of $(x, y)$ on $X \times \{-1, 1\}$, with marginal $\nu_X$, and assume $0 < P(y = 1 \mid x) < 1$ for $\nu_X$-almost every $x$. Let $F : X \to \mathbb R$ be a measurable current estimate, put $w(x, y) = e^{-yF(x)}$, and let $f$ be the Real AdaBoost step (23)–(24),
--   $$f(x) = \tfrac12 \log \frac{E_w[1_{[y=1]} \mid x]}{E_w[1_{[y=-1]} \mid x]} = \tfrac12 \log \frac{P_w(y = 1 \mid x)}{P_w(y = -1 \mid x)}.$$
--   Then
--
--   1. $f$ minimizes the criterion over the update: $J(F + f) \le J(F + g)$ for every measurable $g : X \to \mathbb R$, where $J(F) = E(e^{-yF(x)})$;
--   2. for $\nu_X$-almost every $x$,
--   $$F(x) + f(x) = \tfrac12 \log \frac{P(y = 1 \mid x)}{P(y = -1 \mid x)},$$
--   the minimizer of Lemma 1.
--
--   Result 2 states that Real AdaBoost fits an additive logistic regression model by stagewise optimization of $J$; item 2 is the paper's remark that the population algorithm "would stop after one iteration".
--
--   **Formalization Note** The assumption $0 < P(y = 1 \mid x) < 1$ is a disclosed addition: without it the weighted class probabilities can vanish, `Real.log 0 = 0` turns $f$ into a junk value, and no minimizer of $J(F + \cdot)$ exists. The paper's "minimizing $J(F(x) + f(x))$ at each $x$" is formalized as minimization of the joint criterion over measurable updates.
-- source:
--   Friedman, Hastie and Tibshirani, Additive logistic regression: a statistical view of boosting, Ann. Statist. 28 (2000), pp. 348–349, Result 2, (23), (24)

import Mathlib
import Definitions.Def_AddLogReg_ExpCrit_Setting

open MeasureTheory ProbabilityTheory

namespace AddLogReg.ExpCrit

/-- Result 2 (pp. 348–349), population version: given a current measurable estimate `F`, the
step `f` of (23)–(24) minimizes `J(F + f)` over measurable `f`, and `F + f` is already the
minimizer (12) of Lemma 1 ("the algorithm as presented would stop after one iteration"). -/
theorem result_2 {X : Type*} [MeasurableSpace X] (ν : Measure (X × Bool))
    [IsProbabilityMeasure ν]
    (hη : ∀ᵐ x ∂ν.fst, 0 < condProb ν true x ∧ condProb ν true x < 1)
    (F : X → ℝ) (hF : Measurable F) :
    (∀ f : X → ℝ, Measurable f → J ν (F + realStep ν F) ≤ J ν (F + f)) ∧
    (∀ᵐ x ∂ν.fst, F x + realStep ν F x = halfLogit ν x) := by sorry

end AddLogReg.ExpCrit
