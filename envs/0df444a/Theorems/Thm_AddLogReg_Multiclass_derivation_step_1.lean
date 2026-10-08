-- Prove2me | Theorems.Thm_AddLogReg_Multiclass_derivation_step_1
-- name    : AddLogReg.Multiclass.derivation_step_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T23:04:40.316989+00:00
-- url     : https://prove2.me/theorems/336ef0c4-95a0-4dd9-8317-10f63d7a6660
-- title:
--   Derivation of Result 6, step 1, p. 357 — E(l(G+g)|x), the score s_j = E(y*_j − p_j|x) and the Hessian H_{jk} = −p_j(δ_{jk} − p_k)
-- statement:
--   Let $\nu$ be a probability measure on $X\times\{1,\dots,J\}$, the joint law of the feature $x$ and the class, with indicator responses $y^*_j$. Let $F(x) = (F_1(x),\dots,F_J(x))$ be the current fit with model probabilities $p_j(x) = e^{F_j(x)}/\sum_k e^{F_k(x)}$, fix $x$ and a base class $b$, and let $G_j(x) = F_j(x)-F_b(x)$. For an update $g$ (with $g_b$ irrelevant) write
--   $$\Lambda(g) = E\big(l(G+g)\mid x\big),\qquad l(G) = \sum_{j\ne b} y^*_jG_j - \log\Big(1+\sum_{k\ne b}e^{G_k}\Big).$$
--   Then:
--
--   1. the expected conditional log-likelihood is
--   $$E\big(l(G+g)\mid x\big) = \sum_{j\ne b} E(y^*_j\mid x)\big(G_j(x)+g_j\big) - \log\Big(1+\sum_{k\ne b}e^{G_k(x)+g_k}\Big);$$
--   2. for $j\ne b$ the **score** is the partial derivative at $g=0$:
--   $$s_j(x) = \frac{\partial \Lambda}{\partial g_j}\Big|_{g=0} = E\big(y^*_j - p_j(x)\mid x\big);$$
--   3. for $j\ne b$ and every $g$, the partial derivative of $\Lambda$ in $g_j$ at $g$ is
--   $$\partial_j\Lambda(g) = E(y^*_j\mid x) - \frac{e^{G_j(x)+g_j}}{1+\sum_{k\ne b}e^{G_k(x)+g_k}} ;$$
--   4. for $j,k\ne b$ the **Hessian** is the partial derivative of $\partial_j\Lambda$ in $g_k$ at $g = 0$:
--   $$H_{j,k}(x) = -p_j(x)\big(\delta_{jk}-p_k(x)\big).$$
--
--   These are the score and Hessian of the population Newton algorithm for the multinomial log-likelihood in multilogit coordinates, the first step of the derivation that J-class LogitBoost takes quasi-Newton steps.
--
--   **Formalization Note** Conditional expectations given $x$ are integrals against `ν.condKernel x`. Partial derivatives are `HasDerivAt` along a coordinate line `Function.update g j (g j + t)` at $t=0$; the second derivative is taken of the explicit first partial derivative, which item 3 shows is the partial derivative at every $g$. The page takes $b = J$; here $b$ is arbitrary.
-- source:
--   Friedman, Hastie and Tibshirani, Additive logistic regression: a statistical view of boosting, Ann. Statist. 28 (2000), p. 357, Derivation of Result 6, step 1

import Mathlib
import Definitions.Def_AddLogReg_Multiclass_Setting

open MeasureTheory ProbabilityTheory ENNReal

namespace AddLogReg.Multiclass

theorem derivation_step_1 {J : ℕ} [NeZero J] {X : Type*} [MeasurableSpace X]
    (ν : Measure (X × Fin J)) [IsProbabilityMeasure ν] (F : X → Fin J → ℝ) (x : X) (b : Fin J) :
    (∀ g : Fin J → ℝ, baseLogLik ν F x b g =
        ∑ j ∈ Finset.univ.erase b, (∫ y, ystar y j ∂(ν.condKernel x)) * (F x j - F x b + g j) -
          Real.log (1 + ∑ k ∈ Finset.univ.erase b, Real.exp (F x k - F x b + g k))) ∧
      (∀ j, j ≠ b → HasDerivAt (fun t : ℝ => baseLogLik ν F x b (Function.update 0 j t))
        (score ν F x j) 0) ∧
      (∀ j, j ≠ b → ∀ g : Fin J → ℝ,
        HasDerivAt (fun t : ℝ => baseLogLik ν F x b (Function.update g j (g j + t)))
          (gradBase ν F x b g j) 0) ∧
      (∀ j k, j ≠ b → k ≠ b →
        HasDerivAt (fun t : ℝ => gradBase ν F x b (Function.update 0 k t) j) (hess F x j k) 0) := by sorry

end AddLogReg.Multiclass
