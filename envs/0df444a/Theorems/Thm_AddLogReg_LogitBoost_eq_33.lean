-- Prove2me | Theorems.Thm_AddLogReg_LogitBoost_eq_33
-- name    : AddLogReg.LogitBoost.eq_33
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T00:02:49.973191+00:00
-- url     : https://prove2.me/theorems/84171baf-03f2-44c8-abc6-ed7c77319c71
-- title:
--   (33), p. 352 — H(x) = ∂²E[l(F+f)|x]/∂f(x)² at f(x)=0 equals −4E(p(x)(1 − p(x))|x)
-- statement:
--   In the setting of (32), with $\ell_x(t)$ the conditional expected log-likelihood of the update $F(x)+t$ and $p(u) = e^{u}/(e^{u}+e^{-u})$:
--
--   1. for every $t\in\mathbb R$, $\ell_x$ is differentiable at $t$ with
--   $$\ell_x'(t) = 2E\big(y^*-p(F(x)+t)\mid x\big);$$
--   2. this derivative function is differentiable at $t = 0$ with
--   $$H(x) = \frac{\partial^2 E\,l(F(x)+f(x))}{\partial f(x)^2}\Big|_{f(x)=0} = -4E\big(p(x)(1-p(x))\mid x\big),$$
--   where $p(x) = p(F(x))$ is defined in terms of $F(x)$.
--
--   This is the Hessian of the Newton step in the Derivation of Result 3.
--
--   **Formalization Note** The second derivative is stated as the derivative at $0$ of an explicit function that is shown to be the first derivative at every $t$, rather than with `deriv`, which returns $0$ at non-differentiable points. $H(x)$ is kept as the page prints it, as a conditional expectation of $p(x)(1-p(x))$, even though that quantity depends on $x$ only.
-- source:
--   Friedman, Hastie and Tibshirani, Additive logistic regression: a statistical view of boosting, Ann. Statist. 28 (2000), p. 352, (33)

import Mathlib
import Definitions.Def_AddLogReg_LogitBoost_Setting

open MeasureTheory ProbabilityTheory

namespace AddLogReg.LogitBoost

theorem eq_33 {X : Type*} [MeasurableSpace X] (ν : Measure (X × Bool)) [IsProbabilityMeasure ν]
    (F : X → ℝ) (x : X) :
    (∀ t : ℝ, HasDerivAt (condLogLik ν F x)
        (2 * ∫ b, (ystar b - symLogistic (F x + t)) ∂(ν.condKernel x)) t) ∧
      HasDerivAt (fun t : ℝ => 2 * ∫ b, (ystar b - symLogistic (F x + t)) ∂(ν.condKernel x))
        (-4 * ∫ _b, symLogistic (F x) * (1 - symLogistic (F x)) ∂(ν.condKernel x)) 0 := by sorry

end AddLogReg.LogitBoost
