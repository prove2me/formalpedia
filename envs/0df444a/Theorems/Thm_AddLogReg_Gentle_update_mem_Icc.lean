-- Prove2me | Theorems.Thm_AddLogReg_Gentle_update_mem_Icc
-- name    : AddLogReg.Gentle.update_mem_Icc
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T01:08:50.578427+00:00
-- url     : https://prove2.me/theorems/dd7c5528-2ded-4229-a9bd-efaa45773551
-- title:
--   §4.4, p. 354 — the Gentle AdaBoost update E_w(y|x) lies in [−1, 1]
-- statement:
--   Let $\nu$ be a probability measure on $X\times\{-1,1\}$, the joint law of $(x,y)$, let $F : X\to\mathbb R$, fix $x\in X$, and let $w(x,y) = e^{-yF(x)}$. The population Gentle AdaBoost increment lies in the unit interval around $0$:
--   $$-1 \le E_w(y\mid x) \le 1.$$
--
--   The paper contrasts this with the log-ratio update of Real AdaBoost, which can be arbitrarily large in pure regions.
-- source:
--   Friedman, Hastie and Tibshirani, Additive logistic regression: a statistical view of boosting, Ann. Statist. 28 (2000), p. 354, §4.4, first paragraph

import Mathlib
import Definitions.Def_AddLogReg_Gentle_Setting

open MeasureTheory ProbabilityTheory

namespace AddLogReg.Gentle

theorem update_mem_Icc {X : Type*} [MeasurableSpace X] (ν : Measure (X × Bool))
    [IsProbabilityMeasure ν] (F : X → ℝ) (x : X) :
    AddLogReg.ExpCrit.wCondExp ν F (fun _ b => AddLogReg.ExpCrit.sgn b) x ∈ Set.Icc (-1 : ℝ) 1 := by sorry

end AddLogReg.Gentle
