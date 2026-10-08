-- Prove2me | Theorems.Thm_AddLogReg_Gentle_newton_update
-- name    : AddLogReg.Gentle.newton_update
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T01:08:49.359765+00:00
-- url     : https://prove2.me/theorems/a433a34a-5250-4ce1-b858-9e8922c88895
-- title:
--   Derivation of Result 4, p. 353 — F(x) + E(e^{−yF(x)}y|x)/E(e^{−yF(x)}|x) = F(x) + E_w(y|x), w = e^{−yF(x)}
-- statement:
--   Let $\nu$ be a probability measure on $X\times\{-1,1\}$, the joint law of $(x,y)$, let $F : X\to\mathbb R$ and fix $x\in X$. With the weight $w(x,y) = e^{-yF(x)}$ and the weighted conditional expectation $E_w[g\mid x] = E[wg\mid x]/E[w\mid x]$,
--   $$F(x) + \frac{E\big(e^{-yF(x)}y\mid x\big)}{E\big(e^{-yF(x)}\mid x\big)} = F(x) + E_w(y\mid x).$$
--
--   The left-hand side is the Newton update for $E e^{-yF(x)}$ computed from the Derivation's first and second derivatives; the identity recognizes it as the population form of the Gentle AdaBoost step.
--
--   **Formalization Note** The page's assignment "$F(x) \leftarrow \dots$" is rendered as an equality of the two right-hand sides. Conditional expectations are integrals against `ν.condKernel x`.
-- source:
--   Friedman, Hastie and Tibshirani, Additive logistic regression: a statistical view of boosting, Ann. Statist. 28 (2000), p. 353, §4.4, Derivation of Result 4, third display

import Mathlib
import Definitions.Def_AddLogReg_Gentle_Setting

open MeasureTheory ProbabilityTheory

namespace AddLogReg.Gentle

theorem newton_update {X : Type*} [MeasurableSpace X] (ν : Measure (X × Bool))
    [IsProbabilityMeasure ν] (F : X → ℝ) (x : X) :
    F x + (∫ b, Real.exp (-(AddLogReg.ExpCrit.sgn b * F x)) * AddLogReg.ExpCrit.sgn b ∂(ν.condKernel x)) /
        (∫ b, Real.exp (-(AddLogReg.ExpCrit.sgn b * F x)) ∂(ν.condKernel x)) =
      F x + AddLogReg.ExpCrit.wCondExp ν F (fun _ b => AddLogReg.ExpCrit.sgn b) x := by sorry

end AddLogReg.Gentle
