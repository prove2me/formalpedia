-- Prove2me | Theorems.Thm_AddLogReg_LogitBoost_eq_34_35
-- name    : AddLogReg.LogitBoost.eq_34_35
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T00:02:56.38698+00:00
-- url     : https://prove2.me/theorems/28e945ec-06ec-4618-b183-b704503b76d5
-- title:
--   (34)–(35), p. 352 — F(x) − H(x)⁻¹s(x) = F(x) + ½E(y*−p|x)/E(p(1−p)|x) = F(x) + ½E_w((y*−p)/(p(1−p))|x)
-- statement:
--   Let $\nu$ be a probability measure on $X\times\{0,1\}$, $F : X\to\mathbb R$, $p(x) = e^{F(x)}/(e^{F(x)}+e^{-F(x)})$, and let
--   $$s(x) = 2E\big(y^*-p(x)\mid x\big),\qquad H(x) = -4E\big(p(x)(1-p(x))\mid x\big)$$
--   be the score (32) and Hessian (33). Then $H(x)\neq 0$, and the Newton update satisfies
--   $$F(x) - H(x)^{-1}s(x) = F(x) + \frac12\,\frac{E(y^*-p(x)\mid x)}{E(p(x)(1-p(x))\mid x)} = F(x) + \frac12 E_w\!\left(\frac{y^*-p(x)}{p(x)(1-p(x))}\ \Big|\ x\right),$$
--   where $E_w$ is the weighted conditional expectation with weight $w(x) = p(x)(1-p(x))$.
--
--   The last expression is $F(x)$ plus one half of the population weighted least-squares fit of the working response $z$ of Algorithm 3, which is what identifies LogitBoost's step with a Newton step.
--
--   **Formalization Note** $H(x)\neq0$ is part of the conclusion, not a hypothesis: it holds because $0<p(x)<1$. Without it the Lean division $s/H$ would silently return $0$.
-- source:
--   Friedman, Hastie and Tibshirani, Additive logistic regression: a statistical view of boosting, Ann. Statist. 28 (2000), p. 352, (34)–(35)

import Mathlib
import Definitions.Def_AddLogReg_LogitBoost_Setting

open MeasureTheory ProbabilityTheory

namespace AddLogReg.LogitBoost

theorem eq_34_35 {X : Type*} [MeasurableSpace X] (ν : Measure (X × Bool))
    [IsProbabilityMeasure ν] (F : X → ℝ) (x : X) :
    (-4 * ∫ _b, symLogistic (F x) * (1 - symLogistic (F x)) ∂(ν.condKernel x) ≠ 0) ∧
      F x - (2 * ∫ b, (ystar b - symLogistic (F x)) ∂(ν.condKernel x)) /
          (-4 * ∫ _b, symLogistic (F x) * (1 - symLogistic (F x)) ∂(ν.condKernel x)) =
        F x + (1 / 2) * ((∫ b, (ystar b - symLogistic (F x)) ∂(ν.condKernel x)) /
          ∫ _b, symLogistic (F x) * (1 - symLogistic (F x)) ∂(ν.condKernel x)) ∧
      F x + (1 / 2) * ((∫ b, (ystar b - symLogistic (F x)) ∂(ν.condKernel x)) /
          ∫ _b, symLogistic (F x) * (1 - symLogistic (F x)) ∂(ν.condKernel x)) =
        F x + (1 / 2) * wCondExpBy ν (logitWeight F) (workingResponse F) x := by sorry

end AddLogReg.LogitBoost
