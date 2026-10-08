-- Prove2me | Theorems.Thm_AddLogReg_Gentle_result_4
-- name    : AddLogReg.Gentle.result_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T01:09:36.990373+00:00
-- url     : https://prove2.me/theorems/e01c07da-efd0-4de7-ada1-357503b5ac05
-- title:
--   Result 4, p. 353 — the Gentle AdaBoost algorithm (population version) uses Newton steps for minimizing Ee^{−yF(x)}
-- statement:
--   Let $\nu$ be a probability measure on $X\times\{-1,1\}$, the joint law of $(x,y)$, let $F : X\to\mathbb R$ be the current fit and fix $x\in X$. Write $J(F(x)+f(x)) = E\big(e^{-y(F(x)+f(x))}\mid x\big)$ as a function of the real number $f(x)$, and let
--   $$s(x) = -E\big(e^{-yF(x)}y\mid x\big),\qquad H(x) = E\big(e^{-yF(x)}\mid x\big).$$
--   Then
--
--   1. $s(x)$ is the derivative of $J$ at $f(x) = 0$;
--   2. the derivative of $J$ at every $f(x) = t$ is $-E\big(e^{-y(F(x)+t)}y\mid x\big)$, and the derivative of this function at $t = 0$ is $H(x)$;
--   3. $H(x) > 0$, so the Newton step is defined;
--   4. the population Gentle AdaBoost update (Algorithm 4: $F(x)\leftarrow F(x)+E_w(y\mid x)$ with $w(x,y) = e^{-yF(x)}$) is exactly the Newton step:
--   $$F(x) + E_w(y\mid x) = F(x) - \frac{s(x)}{H(x)}.$$
--
--   This is Result 4: Gentle AdaBoost replaces the exact minimization of Real AdaBoost by one Newton step on the exponential criterion at each iteration.
--
--   **Formalization Note** "Uses Newton steps" is pinned down as in the paper's Derivation: the update equals $F(x)$ minus first derivative over second derivative of the conditional criterion. Derivatives are `HasDerivAt` statements; positivity of $H(x)$ is proved, not assumed, so the division is never Lean's junk division by zero. The statement holds for every $x$; conditional expectations are integrals against `ν.condKernel x`.
-- source:
--   Friedman, Hastie and Tibshirani, Additive logistic regression: a statistical view of boosting, Ann. Statist. 28 (2000), p. 353, Result 4 and its Derivation; Algorithm 4

import Mathlib
import Definitions.Def_AddLogReg_Gentle_Setting

open MeasureTheory ProbabilityTheory

namespace AddLogReg.Gentle

theorem result_4 {X : Type*} [MeasurableSpace X] (ν : Measure (X × Bool))
    [IsProbabilityMeasure ν] (F : X → ℝ) (x : X) :
    HasDerivAt (condCritAt ν F x)
        (-∫ b, Real.exp (-(AddLogReg.ExpCrit.sgn b * F x)) * AddLogReg.ExpCrit.sgn b ∂(ν.condKernel x)) 0 ∧
      (∀ t : ℝ, HasDerivAt (condCritAt ν F x)
        (-∫ b, Real.exp (-(AddLogReg.ExpCrit.sgn b * (F x + t))) * AddLogReg.ExpCrit.sgn b ∂(ν.condKernel x)) t) ∧
      HasDerivAt (fun t : ℝ => -∫ b, Real.exp (-(AddLogReg.ExpCrit.sgn b * (F x + t))) * AddLogReg.ExpCrit.sgn b ∂(ν.condKernel x))
        (∫ b, Real.exp (-(AddLogReg.ExpCrit.sgn b * F x)) ∂(ν.condKernel x)) 0 ∧
      0 < ∫ b, Real.exp (-(AddLogReg.ExpCrit.sgn b * F x)) ∂(ν.condKernel x) ∧
      gentleStep ν F x =
        F x - (-∫ b, Real.exp (-(AddLogReg.ExpCrit.sgn b * F x)) * AddLogReg.ExpCrit.sgn b ∂(ν.condKernel x)) /
          (∫ b, Real.exp (-(AddLogReg.ExpCrit.sgn b * F x)) ∂(ν.condKernel x)) := by sorry

end AddLogReg.Gentle
