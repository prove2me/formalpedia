-- Prove2me | Theorems.Thm_AddLogReg_Multiclass_result_5
-- name    : AddLogReg.Multiclass.result_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T23:05:25.996979+00:00
-- url     : https://prove2.me/theorems/3f3c1f34-2122-4f5b-9782-81ccade747d4
-- title:
--   Result 5, p. 355 — population AdaBoost.MH fits J uncoupled models G_j(x) = ½ log[p_j(x)/(1 − p_j(x))], each class against the rest
-- statement:
--   Let $\nu$ be a probability measure on $X\times\{1,\dots,J\}$, the joint law of the feature $x$ and the class, with $\{-1,1\}$ responses $y_j$ and class probabilities $p_j(x) = P(y_j=1\mid x)$. Assume $0<p_j(x)<1$ for every $j$ and almost every $x$. Put
--   $$G^\star_j(x) = \frac12\log\frac{p_j(x)}{1-p_j(x)} .$$
--   Then:
--
--   1. for each class $j$ separately, $G^\star_j$ minimizes the two-class criterion of class $j$ against the rest: for every measurable $g : X\to\mathbb R$,
--   $$E\,e^{-y_jG^\star_j(x)} \le E\,e^{-y_j g(x)};$$
--   2. consequently $G^\star = (G^\star_1,\dots,G^\star_J)$ minimizes the population AdaBoost.MH criterion: for every family of measurable $G_j$,
--   $$\sum_{j=1}^J E\,e^{-y_jG^\star_j(x)} \le \sum_{j=1}^J E\,e^{-y_jG_j(x)} .$$
--
--   The criterion is a sum of $J$ uncoupled two-class exponential criteria, so population AdaBoost.MH fits $J$ separate additive logistic models, each class against the rest. Nothing forces the implied probabilities to sum to one.
--
--   **Formalization Note** The expectations are lower Lebesgue integrals in $[0,\infty]$. The hypothesis $0<p_j(x)<1$ a.e. is added because the log-odds is undefined at $0$ and $1$ (Lean's `Real.log 0 = 0` would give a junk value); the page leaves it implicit. The page's "½ log p_j(x)/(1 − p_j(x))" is read as $\frac12\log[p_j(x)/(1-p_j(x))]$.
-- source:
--   Friedman, Hastie and Tibshirani, Additive logistic regression: a statistical view of boosting, Ann. Statist. 28 (2000), p. 355, Result 5, observation 1 and Algorithm 5

import Mathlib
import Definitions.Def_AddLogReg_Multiclass_Setting

open MeasureTheory ProbabilityTheory ENNReal

namespace AddLogReg.Multiclass

theorem result_5 {J : ℕ} [NeZero J] {X : Type*} [MeasurableSpace X]
    (ν : Measure (X × Fin J)) [IsProbabilityMeasure ν]
    (hp : ∀ᵐ x ∂ν.fst, ∀ j, 0 < classProb ν j x ∧ classProb ν j x < 1) :
    (∀ j (g : X → ℝ), Measurable g →
        critOne ν j (fun x => (1 / 2) * Real.log (classProb ν j x / (1 - classProb ν j x))) ≤
          critOne ν j g) ∧
      ∀ G : Fin J → X → ℝ, (∀ j, Measurable (G j)) →
        critMH ν (fun j x => (1 / 2) * Real.log (classProb ν j x / (1 - classProb ν j x))) ≤
          critMH ν G := by sorry

end AddLogReg.Multiclass
