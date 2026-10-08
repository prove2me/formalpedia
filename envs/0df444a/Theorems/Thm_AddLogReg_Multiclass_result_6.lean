-- Prove2me | Theorems.Thm_AddLogReg_Multiclass_result_6
-- name    : AddLogReg.Multiclass.result_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T23:04:49.176989+00:00
-- url     : https://prove2.me/theorems/99e8b8c4-8293-45cf-9a1b-46fee70033ac
-- title:
--   Result 6, p. 356 — J-class LogitBoost (population) takes quasi-Newton steps on the multinomial log-likelihood, averaged over the base class
-- statement:
--   Let $J\ge2$, let $\nu$ be a probability measure on $X\times\{1,\dots,J\}$, the joint law of the feature $x$ and the class, with indicator responses $y^*_j$. Let $F(x) = (F_1(x),\dots,F_J(x))$ be the current additive fit, with model probabilities $p_j(x) = e^{F_j(x)}/\sum_k e^{F_k(x)}$ as in (40). Fix $x$. For a base class $b$ let $G_j(x) = F_j(x)-F_b(x)$ and $\Lambda_b(g) = E\big(l(G+g)\mid x\big)$ the expected conditional multinomial log-likelihood in multilogit coordinates. Then the population LogitBoost step (Algorithm 6) is a quasi-Newton step for maximizing this likelihood, in the following sense.
--
--   1. **Score and Hessian.** For every base class $b$ and $j,k\ne b$: the partial derivative of $\Lambda_b$ in $g_j$ at $g=0$ is $s_j(x) = E(y^*_j-p_j(x)\mid x)$; the partial derivative in $g_j$ at every $g$ is $E(y^*_j\mid x) - e^{G_j+g_j}/(1+\sum_{k\ne b}e^{G_k+g_k})$; and its partial derivative in $g_k$ at $g=0$ is $H_{j,k}(x) = -p_j(x)(\delta_{jk}-p_k(x))$.
--   2. **Diagonal quasi-Newton step.** Every $H_{j,j}(x)\neq0$, and for every base $b$ and $j \ne b$ the diagonal step $g^{(b)}_j = -H_{j,j}(x)^{-1}s_j(x)$ equals $E(y^*_j-p_j(x)\mid x)/\big(p_j(x)(1-p_j(x))\big)$, with $g^{(b)}_b=0$.
--   3. **Averaging over the base class is Algorithm 6.** For every $j$, the updated score of Algorithm 6, steps 2(a)–(b), population version, is
--   $$F_j(x) + \frac{J-1}{J}\Big(f_j(x)-\frac1J\sum_{k=1}^J f_k(x)\Big) = F_j(x) + \frac1J\sum_{b=1}^J\Big(g^{(b)}_j - \frac1J\sum_{k=1}^J g^{(b)}_k\Big),$$
--   where $f_j(x) = E_{w_j}(z_j\mid x)$ is the weighted conditional mean of the working response $z_j = (y^*_j-p_j(x))/(p_j(x)(1-p_j(x)))$ with weight $w_j = p_j(x)(1-p_j(x))$.
--
--   Result 6 states that LogitBoost for $J$ classes, in its population version, uses quasi-Newton steps for fitting an additive symmetric logistic model by maximum likelihood; the derivation on p. 357 pins this down to the three facts above.
--
--   **Formalization Note** Everything is conditional on a fixed $x$ and holds for every $x$; conditional expectations are integrals against `ν.condKernel x`. Derivatives are `HasDerivAt` along coordinate lines, never `deriv` equations. The non-vanishing of $p_j(1-p_j)$ is proved from $J\ge2$, not assumed. No assumption on the true class probabilities is needed.
-- source:
--   Friedman, Hastie and Tibshirani, Additive logistic regression: a statistical view of boosting, Ann. Statist. 28 (2000), p. 356, Result 6 and Algorithm 6; p. 357, Derivation, steps 1–3

import Mathlib
import Definitions.Def_AddLogReg_Multiclass_Setting

open MeasureTheory ProbabilityTheory ENNReal

namespace AddLogReg.Multiclass

theorem result_6 {J : ℕ} [NeZero J] (hJ : 2 ≤ J) {X : Type*} [MeasurableSpace X]
    (ν : Measure (X × Fin J)) [IsProbabilityMeasure ν] (F : X → Fin J → ℝ) (x : X) :
    (∀ b j, j ≠ b →
        HasDerivAt (fun t : ℝ => baseLogLik ν F x b (Function.update 0 j t)) (score ν F x j) 0 ∧
          (∀ g : Fin J → ℝ,
            HasDerivAt (fun t : ℝ => baseLogLik ν F x b (Function.update g j (g j + t)))
              (gradBase ν F x b g j) 0) ∧
          ∀ k, k ≠ b →
            HasDerivAt (fun t : ℝ => gradBase ν F x b (Function.update 0 k t) j) (hess F x j k) 0) ∧
      (∀ j, hess F x j j ≠ 0) ∧
      (∀ b j, j ≠ b → diagStep ν F x b j =
        (∫ y, (ystar y j - softmax (F x) j) ∂(ν.condKernel x)) /
          (softmax (F x) j * (1 - softmax (F x) j))) ∧
      ∀ j, logitBoostJStep ν F x j = F x j + (1 / (J : ℝ)) * ∑ b, symmetrize (diagStep ν F x b) j := by sorry

end AddLogReg.Multiclass
