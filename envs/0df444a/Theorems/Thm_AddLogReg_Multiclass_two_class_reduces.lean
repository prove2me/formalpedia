-- Prove2me | Theorems.Thm_AddLogReg_Multiclass_two_class_reduces
-- name    : AddLogReg.Multiclass.two_class_reduces
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T23:04:36.393835+00:00
-- url     : https://prove2.me/theorems/5b971752-07a6-4bab-9717-694475971e6f
-- title:
--   p. 356 — for J = 2 Algorithm 6 is Algorithm 3: centred F, p = e^F/(e^F + e^{−F}), F ← F + ½ E_w(z|x)
-- statement:
--   Take $J = 2$, a probability measure $\nu$ on $X\times\{1,2\}$, a fit $F(x) = (F_1(x),F_2(x))$ and a point $x$ with $F_1(x)+F_2(x) = 0$. Then, in the population version of Algorithm 6:
--
--   1. the model probability of class 1 is the two-class symmetric logistic (30):
--   $$p_1(x) = \frac{e^{F_1(x)}}{e^{F_1(x)}+e^{-F_1(x)}};$$
--   2. the updated score of class 1 is
--   $$F_1(x) + \tfrac12\,E_{w_1}(z_1\mid x),\qquad z_1 = \frac{y^*_1-p_1(x)}{p_1(x)(1-p_1(x))},\quad w_1 = p_1(x)(1-p_1(x)),$$
--   which is Algorithm 3's update $F(x)\leftarrow F(x)+\frac12 f_m(x)$ with class 1 as $y=1$;
--   3. the update stays centred: the new $F_2(x)$ is minus the new $F_1(x)$.
--
--   This makes precise the sentence "Algorithm 6 is a natural generalization of Algorithm 3 for fitting the J-class logistic regression model (40)".
--
--   **Formalization Note** Classes are `Fin 2`; Algorithm 3's step is written out here, not imported.
-- source:
--   Friedman, Hastie and Tibshirani, Additive logistic regression: a statistical view of boosting, Ann. Statist. 28 (2000), p. 356, sentence before Result 6; p. 351, Algorithm 3 and (30)

import Mathlib
import Definitions.Def_AddLogReg_Multiclass_Setting

open MeasureTheory ProbabilityTheory ENNReal

namespace AddLogReg.Multiclass

theorem two_class_reduces {X : Type*} [MeasurableSpace X]
    (ν : Measure (X × Fin 2)) [IsProbabilityMeasure ν] (F : X → Fin 2 → ℝ) (x : X)
    (hF : F x 0 + F x 1 = 0) :
    softmax (F x) 0 = Real.exp (F x 0) / (Real.exp (F x 0) + Real.exp (-F x 0)) ∧
      logitBoostJStep ν F x 0 =
        F x 0 + (1 / 2) * wCondExpBy ν (fun x' _ => classWeight F x' 0)
          (fun x' y => workingResponse F x' y 0) x ∧
      logitBoostJStep ν F x 1 = -logitBoostJStep ν F x 0 := by sorry

end AddLogReg.Multiclass
