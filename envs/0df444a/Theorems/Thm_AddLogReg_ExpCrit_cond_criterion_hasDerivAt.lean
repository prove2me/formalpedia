-- Prove2me | Theorems.Thm_AddLogReg_ExpCrit_cond_criterion_hasDerivAt
-- name    : AddLogReg.ExpCrit.cond_criterion_hasDerivAt
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T23:05:33.395068+00:00
-- url     : https://prove2.me/theorems/aa27b602-11b6-4d7e-acc2-e124ae3875db
-- title:
--   §4.1, p. 345, proof of Lemma 1 — ∂E(e^{−yF(x)}|x)/∂F(x) = −P(y=1|x)e^{−F(x)} + P(y=−1|x)e^{F(x)}
-- statement:
--   Let $\nu$ be the joint law of $(x, y)$ on $X \times \{-1, 1\}$ and $P(y = \pm 1 \mid x)$ the conditional class probabilities. Fix $x \in X$ and consider the conditional exponential criterion as a function of the value $t = F(x)$, $t \mapsto E(e^{-yt} \mid x)$. It is differentiable at every $t \in \mathbb R$, with derivative
--   $$\frac{\partial E\big(e^{-yF(x)} \mid x\big)}{\partial F(x)} = -P(y = 1 \mid x)\, e^{-F(x)} + P(y = -1 \mid x)\, e^{F(x)}.$$
--
--   This is the second display of the proof of Lemma 1; Lemma 1 follows by setting this derivative to zero.
--
--   **Formalization Note** The derivative is stated with `HasDerivAt`, which asserts differentiability as well as the value, rather than with `deriv`, which returns $0$ at non-differentiable points.
-- source:
--   Friedman, Hastie and Tibshirani, Additive logistic regression: a statistical view of boosting, Ann. Statist. 28 (2000), p. 345, §4.1, proof of Lemma 1, second display

import Mathlib
import Definitions.Def_AddLogReg_ExpCrit_Setting

open MeasureTheory ProbabilityTheory

namespace AddLogReg.ExpCrit

/-- Proof of Lemma 1, second display (p. 345): `∂E(e^{−yF(x)}|x)/∂F(x) =
−P(y = 1|x)e^{−F(x)} + P(y = −1|x)e^{F(x)}`. -/
theorem cond_criterion_hasDerivAt {X : Type*} [MeasurableSpace X] (ν : Measure (X × Bool))
    [IsProbabilityMeasure ν] (x : X) (t : ℝ) :
    HasDerivAt (condCrit ν x)
      (-(condProb ν true x) * Real.exp (-t) + condProb ν false x * Real.exp t) t := by sorry

end AddLogReg.ExpCrit
