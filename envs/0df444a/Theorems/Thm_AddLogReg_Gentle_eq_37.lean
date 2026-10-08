-- Prove2me | Theorems.Thm_AddLogReg_Gentle_eq_37
-- name    : AddLogReg.Gentle.eq_37
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T01:09:05.4613+00:00
-- url     : https://prove2.me/theorems/3310942c-6b03-4f74-897f-ccecc6d0904f
-- title:
--   (37), p. 354 — E(e^{−yF}y|x)/E(e^{−yF}|x) = (P − p(x))/((1 − p(x))P + p(x)(1 − P)), always in [−1, 1]
-- statement:
--   Let $\nu$ be a probability measure on $X\times\{-1,1\}$, the joint law of $(x,y)$, let $F : X\to\mathbb R$ and fix $x\in X$. Let $P = P(y = 1\mid x)$ and let
--   $$p(x) = \frac{e^{F(x)}}{e^{F(x)}+e^{-F(x)}}$$
--   be the symmetric logistic of $F(x)$. Then
--
--   1. $$\frac{E(e^{-yF(x)}y\mid x)}{E(e^{-yF(x)}\mid x)} = \frac{e^{-F(x)}P - e^{F(x)}(1-P)}{e^{-F(x)}P + e^{F(x)}(1-P)};$$
--   2. $$\frac{e^{-F(x)}P - e^{F(x)}(1-P)}{e^{-F(x)}P + e^{F(x)}(1-P)} = \frac{P - p(x)}{(1-p(x))P + p(x)(1-P)};$$
--   3. this common value always lies in $[-1, 1]$.
--
--   Written in terms of $P$ and $p(x)$, the Gentle AdaBoost update can be compared directly with the LogitBoost update (38).
--
--   **Formalization Note** $P(y = -1\mid x) = 1 - P$ is not assumed; it follows from the conditional law being a probability measure. The symmetric logistic is the exact expression above, not $1/(1+e^{-F(x)})$, with which (37) is false.
-- source:
--   Friedman, Hastie and Tibshirani, Additive logistic regression: a statistical view of boosting, Ann. Statist. 28 (2000), p. 354, §4.4, (37) and the paragraph after (38)

import Mathlib
import Definitions.Def_AddLogReg_Gentle_Setting

open MeasureTheory ProbabilityTheory

namespace AddLogReg.Gentle

theorem eq_37 {X : Type*} [MeasurableSpace X] (ν : Measure (X × Bool))
    [IsProbabilityMeasure ν] (F : X → ℝ) (x : X) :
    (∫ b, Real.exp (-(AddLogReg.ExpCrit.sgn b * F x)) * AddLogReg.ExpCrit.sgn b ∂(ν.condKernel x)) /
        (∫ b, Real.exp (-(AddLogReg.ExpCrit.sgn b * F x)) ∂(ν.condKernel x)) =
      (Real.exp (-F x) * AddLogReg.ExpCrit.condProb ν true x - Real.exp (F x) * (1 - AddLogReg.ExpCrit.condProb ν true x)) /
        (Real.exp (-F x) * AddLogReg.ExpCrit.condProb ν true x + Real.exp (F x) * (1 - AddLogReg.ExpCrit.condProb ν true x)) ∧
    (Real.exp (-F x) * AddLogReg.ExpCrit.condProb ν true x - Real.exp (F x) * (1 - AddLogReg.ExpCrit.condProb ν true x)) /
        (Real.exp (-F x) * AddLogReg.ExpCrit.condProb ν true x + Real.exp (F x) * (1 - AddLogReg.ExpCrit.condProb ν true x)) =
      (AddLogReg.ExpCrit.condProb ν true x - AddLogReg.LogitBoost.symLogistic (F x)) /
        ((1 - AddLogReg.LogitBoost.symLogistic (F x)) * AddLogReg.ExpCrit.condProb ν true x +
          AddLogReg.LogitBoost.symLogistic (F x) * (1 - AddLogReg.ExpCrit.condProb ν true x)) ∧
    (AddLogReg.ExpCrit.condProb ν true x - AddLogReg.LogitBoost.symLogistic (F x)) /
        ((1 - AddLogReg.LogitBoost.symLogistic (F x)) * AddLogReg.ExpCrit.condProb ν true x +
          AddLogReg.LogitBoost.symLogistic (F x) * (1 - AddLogReg.ExpCrit.condProb ν true x)) ∈ Set.Icc (-1 : ℝ) 1 := by sorry

end AddLogReg.Gentle
