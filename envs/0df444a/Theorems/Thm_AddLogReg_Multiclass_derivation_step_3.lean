-- Prove2me | Theorems.Thm_AddLogReg_Multiclass_derivation_step_3
-- name    : AddLogReg.Multiclass.derivation_step_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T23:04:48.580991+00:00
-- url     : https://prove2.me/theorems/e62848e4-469f-4407-b79e-4d9771d3f59a
-- title:
--   Derivation of Result 6, step 3, p. 357 — averaging the symmetrized step over all base classes gives f_j = ((J−1)/J)(u_j − (1/J)Σ_k u_k)
-- statement:
--   Let $J\ge2$, let $\nu$ be a probability measure on $X\times\{1,\dots,J\}$, $F(x)$ the current fit with model probabilities $p_j(x)$, and fix $x$. For a base class $b$ let $g^{(b)}$ be the diagonal quasi-Newton step of step 2 in base-$b$ coordinates ($g^{(b)}_b = 0$), and convert it to the symmetric parametrization by
--   $$f^{(b)}_j = g^{(b)}_j - \frac1J\sum_{k=1}^J g^{(b)}_k .$$
--   Write $u_j = E(y^*_j - p_j(x)\mid x)/\big(p_j(x)(1-p_j(x))\big)$. Then the average over all choices of base class is
--   $$\frac1J\sum_{b=1}^J f^{(b)}_j = \Big(\frac{J-1}{J}\Big)\bigg(\frac{E(y^*_j - p_j(x)\mid x)}{p_j(x)(1-p_j(x))} - \frac1J\sum_{k=1}^J \frac{E(y^*_k - p_k(x)\mid x)}{p_k(x)(1-p_k(x))}\bigg).$$
--
--   This is the update of the symmetric J-class LogitBoost: averaging over the base class removes the dependence of the quasi-Newton step on the arbitrary choice of base.
--
--   **Formalization Note** The constants $1/J$ and $(J-1)/J$ are real numbers.
-- source:
--   Friedman, Hastie and Tibshirani, Additive logistic regression: a statistical view of boosting, Ann. Statist. 28 (2000), p. 357, Derivation of Result 6, step 3

import Mathlib
import Definitions.Def_AddLogReg_Multiclass_Setting

open MeasureTheory ProbabilityTheory ENNReal

namespace AddLogReg.Multiclass

theorem derivation_step_3 {J : ℕ} [NeZero J] (hJ : 2 ≤ J) {X : Type*} [MeasurableSpace X]
    (ν : Measure (X × Fin J)) [IsProbabilityMeasure ν] (F : X → Fin J → ℝ) (x : X) (j : Fin J) :
    (1 / (J : ℝ)) * ∑ b, symmetrize (diagStep ν F x b) j =
      (((J : ℝ) - 1) / (J : ℝ)) *
        ((∫ y, (ystar y j - softmax (F x) j) ∂(ν.condKernel x)) /
            (softmax (F x) j * (1 - softmax (F x) j)) -
          (1 / (J : ℝ)) * ∑ k, (∫ y, (ystar y k - softmax (F x) k) ∂(ν.condKernel x)) /
            (softmax (F x) k * (1 - softmax (F x) k))) := by sorry

end AddLogReg.Multiclass
