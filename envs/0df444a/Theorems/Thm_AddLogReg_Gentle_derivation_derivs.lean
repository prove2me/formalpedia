-- Prove2me | Theorems.Thm_AddLogReg_Gentle_derivation_derivs
-- name    : AddLogReg.Gentle.derivation_derivs
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T01:08:49.876666+00:00
-- url     : https://prove2.me/theorems/7c9ad27b-de72-4f2d-97af-c93b2329c98a
-- title:
--   Derivation of Result 4, p. 353 — first and second derivatives of E(e^{−y(F(x)+f(x))}|x) at f(x) = 0
-- statement:
--   Let $\nu$ be a probability measure on $X\times\{-1,1\}$, the joint law of $(x,y)$, let $F : X\to\mathbb R$ and fix $x\in X$. Write $J(F(x)+f(x)) = E\big(e^{-y(F(x)+f(x))}\mid x\big)$, a function of the real number $f(x)$. Then
--
--   1. $J$ is differentiable at $f(x) = 0$ with
--   $$\frac{\partial J(F(x)+f(x))}{\partial f(x)}\bigg|_{f(x)=0} = -E\big(e^{-yF(x)}y\mid x\big);$$
--   2. at every $f(x) = t$ the derivative is $-E\big(e^{-y(F(x)+t)}y\mid x\big)$;
--   3. this first derivative is itself differentiable at $0$, with
--   $$\frac{\partial^2 J(F(x)+f(x))}{\partial f(x)^2}\bigg|_{f(x)=0} = E\big(e^{-yF(x)}y^2\mid x\big) = E\big(e^{-yF(x)}\mid x\big),$$
--   the last equality because $y^2 = 1$.
--
--   These are the gradient and Hessian that the Newton step of Result 4 is built from.
--
--   **Formalization Note** Derivatives are stated with `HasDerivAt`, so differentiability is part of the claim. The second derivative is the derivative at $0$ of the explicit function $t\mapsto -E(e^{-y(F(x)+t)}y\mid x)$, which conjunct 2 shows to be the derivative of $J$ at every $t$. The statement holds for every $x$ (conditional expectations are integrals against the conditional law `ν.condKernel x` on the two-point label set).
-- source:
--   Friedman, Hastie and Tibshirani, Additive logistic regression: a statistical view of boosting, Ann. Statist. 28 (2000), p. 353, §4.4, Derivation of Result 4, first and second displays

import Mathlib
import Definitions.Def_AddLogReg_Gentle_Setting

open MeasureTheory ProbabilityTheory

namespace AddLogReg.Gentle

theorem derivation_derivs {X : Type*} [MeasurableSpace X] (ν : Measure (X × Bool))
    [IsProbabilityMeasure ν] (F : X → ℝ) (x : X) :
    HasDerivAt (condCritAt ν F x)
        (-∫ b, Real.exp (-(AddLogReg.ExpCrit.sgn b * F x)) * AddLogReg.ExpCrit.sgn b ∂(ν.condKernel x)) 0 ∧
      (∀ t : ℝ, HasDerivAt (condCritAt ν F x)
        (-∫ b, Real.exp (-(AddLogReg.ExpCrit.sgn b * (F x + t))) * AddLogReg.ExpCrit.sgn b ∂(ν.condKernel x)) t) ∧
      HasDerivAt (fun t : ℝ => -∫ b, Real.exp (-(AddLogReg.ExpCrit.sgn b * (F x + t))) * AddLogReg.ExpCrit.sgn b ∂(ν.condKernel x))
        (∫ b, Real.exp (-(AddLogReg.ExpCrit.sgn b * F x)) * AddLogReg.ExpCrit.sgn b ^ 2 ∂(ν.condKernel x)) 0 ∧
      ∫ b, Real.exp (-(AddLogReg.ExpCrit.sgn b * F x)) * AddLogReg.ExpCrit.sgn b ^ 2 ∂(ν.condKernel x) =
        ∫ b, Real.exp (-(AddLogReg.ExpCrit.sgn b * F x)) ∂(ν.condKernel x) := by sorry

end AddLogReg.Gentle
