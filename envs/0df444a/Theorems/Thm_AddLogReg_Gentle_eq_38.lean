-- Prove2me | Theorems.Thm_AddLogReg_Gentle_eq_38
-- name    : AddLogReg.Gentle.eq_38
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T01:08:40.453974+00:00
-- url     : https://prove2.me/theorems/c24d4da3-005d-4166-8dab-da23ddf76ae6
-- title:
--   (38), p. 354 — the LogitBoost increment of (34) equals ½ (P − p(x))/(p(x)(1 − p(x)))
-- statement:
--   Let $\nu$ be a probability measure on $X\times\{-1,1\}$, the joint law of $(x,y)$, let $y^* = (y+1)/2$, let $F : X\to\mathbb R$ and fix $x\in X$. Let $P = P(y = 1\mid x)$ and $p(x) = e^{F(x)}/(e^{F(x)}+e^{-F(x)})$. The LogitBoost increment of (34) is, written with $P$,
--   $$\frac12\,\frac{E\big(y^*-p(x)\mid x\big)}{E\big(p(x)(1-p(x))\mid x\big)} = \frac12\,\frac{P - p(x)}{p(x)(1-p(x))}.$$
--
--   This is the expression the paper compares with the Gentle AdaBoost update (37).
--
--   **Formalization Note** The left-hand side restates the increment of (34) locally (that display belongs to the LogitBoost mission). $p(x)$ depends on $x$ only, so $E(p(x)(1-p(x))\mid x) = p(x)(1-p(x))$; this is part of what is to be shown.
-- source:
--   Friedman, Hastie and Tibshirani, Additive logistic regression: a statistical view of boosting, Ann. Statist. 28 (2000), p. 354, §4.4, (38); p. 352, (34)

import Mathlib
import Definitions.Def_AddLogReg_Gentle_Setting

open MeasureTheory ProbabilityTheory

namespace AddLogReg.Gentle

theorem eq_38 {X : Type*} [MeasurableSpace X] (ν : Measure (X × Bool))
    [IsProbabilityMeasure ν] (F : X → ℝ) (x : X) :
    (1 / 2) * ((∫ b, (AddLogReg.LogitBoost.ystar b - AddLogReg.LogitBoost.symLogistic (F x)) ∂(ν.condKernel x)) /
        ∫ _b, AddLogReg.LogitBoost.symLogistic (F x) * (1 - AddLogReg.LogitBoost.symLogistic (F x)) ∂(ν.condKernel x)) =
      (1 / 2) * ((AddLogReg.ExpCrit.condProb ν true x - AddLogReg.LogitBoost.symLogistic (F x)) /
        (AddLogReg.LogitBoost.symLogistic (F x) * (1 - AddLogReg.LogitBoost.symLogistic (F x)))) := by sorry

end AddLogReg.Gentle
