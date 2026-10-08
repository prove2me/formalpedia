-- Prove2me | Theorems.Thm_AddLogReg_LogitBoost_eq_36
-- name    : AddLogReg.LogitBoost.eq_36
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T00:03:08.338321+00:00
-- url     : https://prove2.me/theorems/49d4b367-1d77-46f5-ae94-bf4f8ce432e9
-- title:
--   (36), p. 352 — the Newton update f(x) solves the weighted least-squares problem min E_w(F + ½z − (F + f))²
-- statement:
--   Let $\nu$ be a probability measure on $X\times\{0,1\}$, $F : X\to\mathbb R$, $p(x) = e^{F(x)}/(e^{F(x)}+e^{-F(x)})$, $z = (y^*-p(x))/(p(x)(1-p(x)))$ the working response and $w(x) = p(x)(1-p(x))$ the weight of Algorithm 3. Let
--   $$f_N(x) = -H(x)^{-1}s(x) = -\frac{2E(y^*-p(x)\mid x)}{-4E(p(x)(1-p(x))\mid x)}$$
--   be the Newton update of (34). Then $f_N(x)$ solves the weighted least-squares approximation about $F(x)$ to the log-likelihood,
--   $$\min_{f(x)} E_{w(x)}\Big(F(x) + \frac12\,\frac{y^*-p(x)}{p(x)(1-p(x))} - \big(F(x)+f(x)\big)\Big)^2,$$
--   that is, for every real $t$,
--   $$E_w\Big[\big(F(x)+\tfrac12 z - (F(x)+f_N(x))\big)^2\,\Big|\,x\Big] \le E_w\Big[\big(F(x)+\tfrac12 z - (F(x)+t)\big)^2\,\Big|\,x\Big];$$
--   and $F(x)+f_N(x)$ is the population LogitBoost update $F(x)+\frac12E_w(z\mid x)$ of Algorithm 3.
--
--   **Formalization Note** The page writes the weighted expectation in (36) as $E_{w(x)}$ without "$\mid x$"; since the Derivation conditions on $x$ throughout and $w(x)$ depends on $x$ only, it is read as the conditional weighted expectation $E_w(\cdot\mid x)$.
-- source:
--   Friedman, Hastie and Tibshirani, Additive logistic regression: a statistical view of boosting, Ann. Statist. 28 (2000), p. 352, (36)

import Mathlib
import Definitions.Def_AddLogReg_LogitBoost_Setting

open MeasureTheory ProbabilityTheory

namespace AddLogReg.LogitBoost

theorem eq_36 {X : Type*} [MeasurableSpace X] (ν : Measure (X × Bool)) [IsProbabilityMeasure ν]
    (F : X → ℝ) (x : X) :
    (∀ t : ℝ,
      wCondExpBy ν (logitWeight F)
          (fun x' b => (F x' + (1 / 2) * workingResponse F x' b -
            (F x' + -((2 * ∫ b', (ystar b' - symLogistic (F x)) ∂(ν.condKernel x)) /
              (-4 * ∫ _b', symLogistic (F x) * (1 - symLogistic (F x)) ∂(ν.condKernel x))))) ^ 2) x ≤
        wCondExpBy ν (logitWeight F)
          (fun x' b => (F x' + (1 / 2) * workingResponse F x' b - (F x' + t)) ^ 2) x) ∧
      F x + -((2 * ∫ b, (ystar b - symLogistic (F x)) ∂(ν.condKernel x)) /
          (-4 * ∫ _b, symLogistic (F x) * (1 - symLogistic (F x)) ∂(ν.condKernel x))) =
        logitBoostStep ν F x := by sorry

end AddLogReg.LogitBoost
