-- Prove2me | Theorems.Thm_AddLogReg_Multiclass_base_probs
-- name    : AddLogReg.Multiclass.base_probs
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T23:04:56.543034+00:00
-- url     : https://prove2.me/theorems/ee89d720-ccb5-45f0-b6d3-b0bf2f4b4aca
-- title:
--   Derivation of Result 6, step 1, p. 357 — multilogit coordinates G_j = F_j − F_b with base class b give the probabilities (40) and G_j = log(p_j/p_b)
-- statement:
--   Let $F=(F_1,\dots,F_J)$ be a real vector, let $p_j = e^{F_j}/\sum_{k=1}^J e^{F_k}$ be its probabilities (40), and fix a **base class** $b$. Put $G_j = F_j - F_b$, so that $G_b = 0$. Then for every $j\ne b$,
--   $$\frac{e^{G_j}}{1+\sum_{k\ne b} e^{G_k}} = p_j,\qquad \frac{1}{1+\sum_{k\ne b}e^{G_k}} = p_b,\qquad G_j = \log\frac{p_j}{p_b}.$$
--
--   So the multilogit parametrization $G_j(x) = \log[P(y^*_j = 1\mid x)/P(y^*_b=1\mid x)]$, $G_b(x)=0$, used in step 1 of the Derivation of Result 6, describes the same probabilities as the symmetric parametrization (40); this is what allows the score and Hessian of step 1 to be written in terms of $p_j(x)$.
--
--   **Formalization Note** The page takes $b = J$ and remarks that the choice of base class is arbitrary; here $b$ is any class. The statement is about the values at a fixed $x$.
-- source:
--   Friedman, Hastie and Tibshirani, Additive logistic regression: a statistical view of boosting, Ann. Statist. 28 (2000), p. 357, Derivation of Result 6, step 1, first display (multilogit parametrization G_j(x))

import Mathlib
import Definitions.Def_AddLogReg_Multiclass_Setting

open MeasureTheory ProbabilityTheory ENNReal

namespace AddLogReg.Multiclass

theorem base_probs {J : ℕ} (F : Fin J → ℝ) (b j : Fin J) (hj : j ≠ b) :
    Real.exp (F j - F b) / (1 + ∑ k ∈ Finset.univ.erase b, Real.exp (F k - F b)) = softmax F j ∧
      1 / (1 + ∑ k ∈ Finset.univ.erase b, Real.exp (F k - F b)) = softmax F b ∧
      Real.log (softmax F j / softmax F b) = F j - F b := by sorry

end AddLogReg.Multiclass
