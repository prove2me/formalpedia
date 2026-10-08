-- Prove2me | Theorems.Thm_AddLogReg_Multiclass_def_1_two_class
-- name    : AddLogReg.Multiclass.def_1_two_class
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T23:05:28.017103+00:00
-- url     : https://prove2.me/theorems/996b0c22-4334-49a1-a84f-11ba7f2a8518
-- title:
--   Definition 1, p. 354 — for J = 2 the symmetric multiple logistic transformation is the two-class ½ log[p/(1−p)] and (40) is (13)
-- statement:
--   Take $J = 2$ classes. Let $p=(p_1,p_2)$ with $p_1,p_2>0$ and $p_1+p_2 = 1$, and let $F = (F_1,F_2)$ be a real vector with $F_1+F_2 = 0$. Then:
--
--   1. the transformation (39) is the two-class symmetric log-odds of (12), and is antisymmetric:
--   $$F_1(p) = \frac12\log\frac{p_1}{p_2},\qquad F_2(p) = -F_1(p),$$
--   where $F_j(p) = \log p_j - \frac12(\log p_1+\log p_2)$;
--   2. the probabilities (40) are the two-class symmetric logistic (13):
--   $$\frac{e^{F_1}}{e^{F_1}+e^{F_2}} = \frac{e^{F_1}}{e^{F_1}+e^{-F_1}},\qquad \frac{e^{F_2}}{e^{F_1}+e^{F_2}} = 1-\frac{e^{F_1}}{e^{F_1}+e^{F_2}} .$$
--
--   This is "the equivalence with the two-class case" asserted after Definition 1: with class 1 as $y=1$, the multiclass parametrization reduces to $F(x) = \frac12\log[P(y=1\mid x)/P(y=-1\mid x)]$ and $p(x) = e^{F(x)}/(e^{F(x)}+e^{-F(x)})$ of §4.
--
--   **Formalization Note** Classes are `Fin 2` with $0$ playing class 1 and $1$ playing class 2.
-- source:
--   Friedman, Hastie and Tibshirani, Additive logistic regression: a statistical view of boosting, Ann. Statist. 28 (2000), p. 354, Definition 1, last sentence ("as well as the equivalence with the two-class case"); p. 345, (12)–(13)

import Mathlib
import Definitions.Def_AddLogReg_Multiclass_Setting

open MeasureTheory ProbabilityTheory ENNReal

namespace AddLogReg.Multiclass

theorem def_1_two_class (p : Fin 2 → ℝ) (hp_pos : ∀ j, 0 < p j) (hp_sum : ∑ j, p j = 1)
    (F : Fin 2 → ℝ) (hF : F 0 + F 1 = 0) :
    symMultiLogit p 0 = (1 / 2) * Real.log (p 0 / p 1) ∧
      symMultiLogit p 1 = -symMultiLogit p 0 ∧
      softmax F 0 = Real.exp (F 0) / (Real.exp (F 0) + Real.exp (-F 0)) ∧
      softmax F 1 = 1 - softmax F 0 := by sorry

end AddLogReg.Multiclass
