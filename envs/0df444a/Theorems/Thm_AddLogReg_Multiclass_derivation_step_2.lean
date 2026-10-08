-- Prove2me | Theorems.Thm_AddLogReg_Multiclass_derivation_step_2
-- name    : AddLogReg.Multiclass.derivation_step_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T23:05:25.251001+00:00
-- url     : https://prove2.me/theorems/0215a4fa-86bd-448f-933f-b49c9b376066
-- title:
--   Derivation of Result 6, step 2, p. 357 — the diagonal quasi-Newton update g_j ← E(y*_j − p_j|x)/(p_j(1 − p_j))
-- statement:
--   Let $J\ge 2$, let $\nu$ be a probability measure on $X\times\{1,\dots,J\}$ and $F(x)$ the current fit with model probabilities $p_j(x)$ given by (40). Fix $x$. With the score $s_j(x) = E(y^*_j-p_j(x)\mid x)$ and Hessian $H_{j,k}(x) = -p_j(x)(\delta_{jk}-p_k(x))$ of step 1:
--
--   1. every diagonal entry of the Hessian is nonzero, $H_{j,j}(x) = -p_j(x)(1-p_j(x)) \ne 0$;
--   2. for every base class $b$ and every $j\ne b$, the Newton step with the Hessian replaced by its diagonal, $g_j = -H_{j,j}(x)^{-1}s_j(x)$, is
--   $$g_j(x) = \frac{E\big(y^*_j-p_j(x)\mid x\big)}{p_j(x)\big(1-p_j(x)\big)} .$$
--
--   This is the quasi-Newton update of the Derivation: a diagonal approximation to the Hessian of step 1. It is not the full Newton step $-H^{-1}s$.
--
--   **Formalization Note** The non-vanishing of $p_j(1-p_j)$ is proved, not assumed: the model probabilities (40) lie strictly between $0$ and $1$ when $J\ge2$. The base coordinate of the step is set to $g_b = 0$.
-- source:
--   Friedman, Hastie and Tibshirani, Additive logistic regression: a statistical view of boosting, Ann. Statist. 28 (2000), p. 357, Derivation of Result 6, step 2

import Mathlib
import Definitions.Def_AddLogReg_Multiclass_Setting

open MeasureTheory ProbabilityTheory ENNReal

namespace AddLogReg.Multiclass

theorem derivation_step_2 {J : ℕ} [NeZero J] (hJ : 2 ≤ J) {X : Type*} [MeasurableSpace X]
    (ν : Measure (X × Fin J)) [IsProbabilityMeasure ν] (F : X → Fin J → ℝ) (x : X) :
    (∀ j, hess F x j j ≠ 0) ∧
      ∀ b j, j ≠ b → diagStep ν F x b j =
        (∫ y, (ystar y j - softmax (F x) j) ∂(ν.condKernel x)) /
          (softmax (F x) j * (1 - softmax (F x) j)) := by sorry

end AddLogReg.Multiclass
