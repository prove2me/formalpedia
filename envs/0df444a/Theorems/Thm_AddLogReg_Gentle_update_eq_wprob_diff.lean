-- Prove2me | Theorems.Thm_AddLogReg_Gentle_update_eq_wprob_diff
-- name    : AddLogReg.Gentle.update_eq_wprob_diff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T01:09:05.173975+00:00
-- url     : https://prove2.me/theorems/9c6f5bdf-ad2c-4c88-8ff8-5c5a2d2e9cb7
-- title:
--   §4.4, p. 353 — the Gentle AdaBoost update is f_m(x) = P_w(y = 1|x) − P_w(y = −1|x)
-- statement:
--   Let $\nu$ be a probability measure on $X\times\{-1,1\}$, the joint law of $(x,y)$, let $F : X\to\mathbb R$, fix $x\in X$, and let $w(x,y) = e^{-yF(x)}$. The population Gentle AdaBoost increment $f_m(x) = E_w(y\mid x)$ is the difference of the weighted class probabilities:
--   $$E_w(y\mid x) = P_w(y = 1\mid x) - P_w(y = -1\mid x),$$
--   where $P_w(y = b\mid x) = E_w[1_{[y=b]}\mid x]$.
--
--   This is how the paper contrasts Gentle AdaBoost with Real AdaBoost, whose increment is half the log-ratio of the same two weighted probabilities.
-- source:
--   Friedman, Hastie and Tibshirani, Additive logistic regression: a statistical view of boosting, Ann. Statist. 28 (2000), pp. 353–354, §4.4, paragraph after the Derivation of Result 4

import Mathlib
import Definitions.Def_AddLogReg_Gentle_Setting

open MeasureTheory ProbabilityTheory

namespace AddLogReg.Gentle

theorem update_eq_wprob_diff {X : Type*} [MeasurableSpace X] (ν : Measure (X × Bool))
    [IsProbabilityMeasure ν] (F : X → ℝ) (x : X) :
    AddLogReg.ExpCrit.wCondExp ν F (fun _ b => AddLogReg.ExpCrit.sgn b) x = wProb ν F true x - wProb ν F false x := by sorry

end AddLogReg.Gentle
