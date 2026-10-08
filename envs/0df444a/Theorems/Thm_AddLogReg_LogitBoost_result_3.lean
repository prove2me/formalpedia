-- Prove2me | Theorems.Thm_AddLogReg_LogitBoost_result_3
-- name    : AddLogReg.LogitBoost.result_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T00:03:01.623344+00:00
-- url     : https://prove2.me/theorems/9e8c65e9-783e-4ae1-bb93-905ed1c40434
-- title:
--   Result 3, p. 352 — population LogitBoost (two classes) uses Newton steps for the additive symmetric logistic model by maximum likelihood
-- statement:
--   **Result 3.** *The LogitBoost algorithm (two classes, population version) uses Newton steps for fitting an additive symmetric logistic model by maximum likelihood.*
--
--   Precisely, as made explicit by the Derivation: let $\nu$ be a probability measure on $X\times\{0,1\}$, the joint law of the feature $x$ and the 0/1 response $y^*$; let $F : X\to\mathbb R$ be the current additive fit and $p(u) = e^{u}/(e^{u}+e^{-u})$ the symmetric logistic (30), with $p(x) = p(F(x))$. Fix $x\in X$ and let
--   $$\ell_x(t) = E\Big[\,2y^*(F(x)+t) - \log\big(1+e^{2(F(x)+t)}\big)\ \Big|\ x\Big]$$
--   be the conditional expected log-likelihood (31) of the update $F(x)+t$. Then
--
--   1. $\ell_x$ has derivative $s(x) = 2E(y^*-p(x)\mid x)$ at $t=0$;
--   2. for every $t$, $\ell_x$ has derivative $2E(y^*-p(F(x)+t)\mid x)$ at $t$, and this derivative function has derivative $H(x) = -4E(p(x)(1-p(x))\mid x)$ at $t = 0$;
--   3. $H(x)\neq 0$;
--   4. the population LogitBoost update of Algorithm 3 — $F(x)+\frac12E_w(z\mid x)$ with working response $z = (y^*-p(x))/(p(x)(1-p(x)))$ and weight $w(x) = p(x)(1-p(x))$ — equals the Newton update
--   $$F(x) - H(x)^{-1}s(x).$$
--
--   This identifies LogitBoost as stagewise Newton–Raphson on the expected Bernoulli log-likelihood of the additive symmetric logistic model, the population counterpart of the iteratively reweighted least squares fit of logistic regression.
--
--   **Formalization Note** Labels are `Bool` with $y^*(\texttt{true}) = 1$, $y^*(\texttt{false}) = 0$; conditional expectations are integrals against Mathlib's regular conditional distribution `ν.condKernel x`, and the statement holds for every $x$. Derivatives are stated with `HasDerivAt`; the second derivative is the derivative of an explicit function shown to be the first derivative everywhere. $H(x)\ne0$ is proved, not assumed. In the population version, step 2(b) (the weighted least-squares regression of $z$ on $x$) is the weighted conditional mean $E_w(z\mid x)$, as the paragraph after (36) explains.
-- source:
--   Friedman, Hastie and Tibshirani, Additive logistic regression: a statistical view of boosting, Ann. Statist. 28 (2000), p. 352, Result 3 and its Derivation (31)–(36); p. 351, (30) and Algorithm 3

import Mathlib
import Definitions.Def_AddLogReg_LogitBoost_Setting

open MeasureTheory ProbabilityTheory

namespace AddLogReg.LogitBoost

theorem result_3 {X : Type*} [MeasurableSpace X] (ν : Measure (X × Bool))
    [IsProbabilityMeasure ν] (F : X → ℝ) (x : X) :
    HasDerivAt (condLogLik ν F x)
        (2 * ∫ b, (ystar b - symLogistic (F x)) ∂(ν.condKernel x)) 0 ∧
      (∀ t : ℝ, HasDerivAt (condLogLik ν F x)
        (2 * ∫ b, (ystar b - symLogistic (F x + t)) ∂(ν.condKernel x)) t) ∧
      HasDerivAt (fun t : ℝ => 2 * ∫ b, (ystar b - symLogistic (F x + t)) ∂(ν.condKernel x))
        (-4 * ∫ _b, symLogistic (F x) * (1 - symLogistic (F x)) ∂(ν.condKernel x)) 0 ∧
      (-4 * ∫ _b, symLogistic (F x) * (1 - symLogistic (F x)) ∂(ν.condKernel x) ≠ 0) ∧
      logitBoostStep ν F x =
        F x - (2 * ∫ b, (ystar b - symLogistic (F x)) ∂(ν.condKernel x)) /
          (-4 * ∫ _b, symLogistic (F x) * (1 - symLogistic (F x)) ∂(ν.condKernel x)) := by sorry

end AddLogReg.LogitBoost
