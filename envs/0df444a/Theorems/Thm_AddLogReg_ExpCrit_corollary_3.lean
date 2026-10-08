-- Prove2me | Theorems.Thm_AddLogReg_ExpCrit_corollary_3
-- name    : AddLogReg.ExpCrit.corollary_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T23:05:26.193984+00:00
-- url     : https://prove2.me/theorems/6ca723c4-3cb8-4c3e-af9c-467a08ab660d
-- title:
--   Corollary 3, p. 349 — at the optimal F(x), the weighted conditional mean of y is 0: E_w(y|x) = 0, w = e^{−yF(x)}
-- statement:
--   Let $\nu$ be the joint law of $(x, y)$ on $X \times \{-1, 1\}$, with marginal $\nu_X$, and let $J(F) = E(e^{-yF(x)})$ be the exponential criterion. Suppose $F : X \to \mathbb R$ is measurable and optimal, i.e. $J(F) \le J(G)$ for every measurable $G : X \to \mathbb R$. Then, for $\nu_X$-almost every $x$, the weighted conditional mean of $y$ with weight $w(x, y) = e^{-yF(x)}$ vanishes:
--   $$E_w(y \mid x) = \frac{E\big[e^{-yF(x)}\, y \mid x\big]}{E\big[e^{-yF(x)} \mid x\big]} = 0.$$
--
--   This is the first-order condition of the exponential criterion at its minimizer: after an optimal fit, the reweighted conditional distribution of $y$ carries no further information about $F$, which is the paper's interpretation of the AdaBoost weights as an alternative to residuals.
--
--   **Formalization Note** The paper's proof display (25) writes the unconditional expectation and "$\partial J(F(x))/F(x)$"; the corollary's own words, "the weighted conditional mean", are what is formalized, as an almost-everywhere statement because conditional probabilities are determined only $\nu_X$-almost everywhere. No assumption on the class probabilities is made: optimality of $F$ already forces them strictly between $0$ and $1$ almost everywhere.
-- source:
--   Friedman, Hastie and Tibshirani, Additive logistic regression: a statistical view of boosting, Ann. Statist. 28 (2000), p. 349, Corollary 3 and (25)

import Mathlib
import Definitions.Def_AddLogReg_ExpCrit_Setting

open MeasureTheory ProbabilityTheory

namespace AddLogReg.ExpCrit

/-- Corollary 3 (p. 349): at the optimal `F(x)`, the weighted conditional mean of `y` is 0,
i.e. `E_w(y|x) = 0` with `w = e^{−yF(x)}`. -/
theorem corollary_3 {X : Type*} [MeasurableSpace X] (ν : Measure (X × Bool))
    [IsProbabilityMeasure ν] (F : X → ℝ) (hF : Measurable F)
    (hopt : ∀ G : X → ℝ, Measurable G → J ν F ≤ J ν G) :
    ∀ᵐ x ∂ν.fst, wCondExp ν F (fun _ b => sgn b) x = 0 := by sorry

end AddLogReg.ExpCrit
