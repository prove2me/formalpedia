-- Prove2me | Theorems.Thm_AddLogReg_Multiclass_algorithm_6_fit
-- name    : AddLogReg.Multiclass.algorithm_6_fit
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T23:04:47.545035+00:00
-- url     : https://prove2.me/theorems/08f6d4bc-81a5-4ac7-8ce6-23c854817f37
-- title:
--   Algorithm 6, step 2(a), p. 356 — the population weighted least-squares fit of z_j with weights p_j(1−p_j) is E(y*_j − p_j|x)/(p_j(1 − p_j))
-- statement:
--   Let $J\ge2$, let $\nu$ be a probability measure on $X\times\{1,\dots,J\}$ and $F(x)$ the current fit with model probabilities $p_j(x)$ given by (40). In Algorithm 6, step 2(a), the working response and weight of class $j$ are
--   $$z_j = \frac{y^*_j - p_j(x)}{p_j(x)(1-p_j(x))},\qquad w_j = p_j(x)(1-p_j(x)),$$
--   and the population version of the weighted least-squares fit of $z_j$ on $x$ is the weighted conditional mean $E_{w_j}(z_j\mid x) = E[w_jz_j\mid x]/E[w_j\mid x]$. For every $x$ and $j$,
--   $$E_{w_j}(z_j\mid x) = \frac{E(y^*_j - p_j(x)\mid x)}{p_j(x)(1-p_j(x))}.$$
--
--   Since the weight depends on $x$ only, the fitted $f_{mj}(x)$ of Algorithm 6 coincides with the diagonal quasi-Newton step of the Derivation of Result 6.
--
--   **Formalization Note** "Population version" replaces the weighted least-squares regression by the weighted conditional expectation, as for Algorithm 3. Conditional expectations are integrals against `ν.condKernel x`.
-- source:
--   Friedman, Hastie and Tibshirani, Additive logistic regression: a statistical view of boosting, Ann. Statist. 28 (2000), p. 356, Algorithm 6, step 2(a); p. 347 (weighted conditional expectation)

import Mathlib
import Definitions.Def_AddLogReg_Multiclass_Setting

open MeasureTheory ProbabilityTheory ENNReal

namespace AddLogReg.Multiclass

theorem algorithm_6_fit {J : ℕ} [NeZero J] (hJ : 2 ≤ J) {X : Type*} [MeasurableSpace X]
    (ν : Measure (X × Fin J)) [IsProbabilityMeasure ν] (F : X → Fin J → ℝ) (x : X) (j : Fin J) :
    wCondExpBy ν (fun x' _ => classWeight F x' j) (fun x' y => workingResponse F x' y j) x =
      (∫ y, (ystar y j - softmax (F x) j) ∂(ν.condKernel x)) /
        (softmax (F x) j * (1 - softmax (F x) j)) := by sorry

end AddLogReg.Multiclass
