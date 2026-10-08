-- Prove2me | Theorems.Thm_AddLogReg_LogitBoost_eq_32
-- name    : AddLogReg.LogitBoost.eq_32
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T00:02:49.264986+00:00
-- url     : https://prove2.me/theorems/a1e04276-38b0-4e20-be76-f2f9baf5d121
-- title:
--   (32), p. 352 — s(x) = ∂E[l(F+f)|x]/∂f(x) at f(x)=0 equals 2E(y* − p(x)|x)
-- statement:
--   Let $\nu$ be a probability measure on $X\times\{0,1\}$, the joint law of $(x, y^*)$, let $F : X\to\mathbb R$ be the current fit and $p(x) = e^{F(x)}/(e^{F(x)}+e^{-F(x)})$. Fix $x\in X$ and consider the conditional expected log-likelihood of the update $F(x)+t$,
--   $$\ell_x(t) = E\Big[\,2y^*(F(x)+t) - \log\big(1+e^{2(F(x)+t)}\big)\ \Big|\ x\Big].$$
--   Then $\ell_x$ is differentiable at $t=0$ with derivative
--   $$s(x) = \frac{\partial E\,l(F(x)+f(x))}{\partial f(x)}\Big|_{f(x)=0} = 2E\big(y^*-p(x)\mid x\big).$$
--
--   This is the score of the Newton step in the Derivation of Result 3.
--
--   **Formalization Note** The derivative is stated with `HasDerivAt`, so the statement includes differentiability. Conditional expectations are integrals against `ν.condKernel x`; the statement holds for every $x$.
-- source:
--   Friedman, Hastie and Tibshirani, Additive logistic regression: a statistical view of boosting, Ann. Statist. 28 (2000), p. 352, (32)

import Mathlib
import Definitions.Def_AddLogReg_LogitBoost_Setting

open MeasureTheory ProbabilityTheory

namespace AddLogReg.LogitBoost

theorem eq_32 {X : Type*} [MeasurableSpace X] (ν : Measure (X × Bool)) [IsProbabilityMeasure ν]
    (F : X → ℝ) (x : X) :
    HasDerivAt (condLogLik ν F x)
      (2 * ∫ b, (ystar b - symLogistic (F x)) ∂(ν.condKernel x)) 0 := by sorry

end AddLogReg.LogitBoost
