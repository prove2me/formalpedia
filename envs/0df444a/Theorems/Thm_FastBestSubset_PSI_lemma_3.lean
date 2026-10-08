-- Prove2me | Theorems.Thm_FastBestSubset_PSI_lemma_3
-- name    : FastBestSubset.PSI.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:07:07.948875+00:00
-- url     : https://prove2.me/theorems/d6d38bdf-b862-4505-90ba-78bb2fb307d7
-- title:
--   Lemma 3 — characterization (8) of CW minima by the thresholding conditions
-- statement:
--   Consider Problem (2) with unit-norm columns of $X$, $\lambda_0>0$ and $\lambda_1,\lambda_2\ge0$. For $\beta^*\in\mathbb R^p$ let $\tilde\beta^*_i=\langle y-\sum_{j\neq i}X_j\beta^*_j,X_i\rangle$. Then $\beta^*$ is a CW minimum if and only if
--
--   1. for every $i\in\operatorname{Supp}(\beta^*)$: $|\tilde\beta^*_i|>\lambda_1$ and
--   $$\beta^*_i=\operatorname{sign}(\tilde\beta^*_i)\frac{|\tilde\beta^*_i|-\lambda_1}{1+2\lambda_2},\qquad |\beta^*_i|\ge\sqrt{\frac{2\lambda_0}{1+2\lambda_2}};$$
--   2. for every $i\notin\operatorname{Supp}(\beta^*)$:
--   $$\frac{|\tilde\beta^*_i|-\lambda_1}{1+2\lambda_2}\le\sqrt{\frac{2\lambda_0}{1+2\lambda_2}} .$$
--
--   Comparing these conditions with the stationarity condition (5) shows that every CW minimum is a stationary solution. That is what the proof of Theorem 4 needs at two places: the outputs of Algorithm 1 are stationary for the restricted least-squares problem on their support, and the final output of Algorithm 2 is stationary.
--
--   **Formalization Note** The clause $|\tilde\beta^*_i|>\lambda_1$ on the support is taken from (5), with which the page compares (8). Without it the literal (8) is false for $\lambda_1>0$. For example, take $\lambda_2=0$ and $|\tilde\beta^*_i|<\lambda_1$ with $\lambda_1-|\tilde\beta^*_i|\ge\sqrt{2\lambda_0}$. Then $\beta^*_i=\operatorname{sign}(\tilde\beta^*_i)(|\tilde\beta^*_i|-\lambda_1)$ satisfies both displayed conditions, but has the sign opposite to $\tilde\beta^*_i$ and does not minimize the coordinate problem, whose minimizer is $0$. $\operatorname{sign}$ is `Real.sign`, so $\operatorname{sign}(0)=0$.
-- source:
--   Hazimeh, Mazumder, Fast Best Subset Selection: Coordinate Descent and Local Combinatorial Optimization Algorithms, arXiv:1803.01454v3, Lemma 3, (8), p. 7 (with (5), p. 6)

import Mathlib
import Definitions.Def_FastBestSubset_CDSS_Setting

namespace FastBestSubset.PSI

/-- Lemma 3 (p. 7), with the condition `|β̃ᵢ| > λ₁` of (5) on the support: `β` is a CW minimum
iff (8) holds. -/
theorem lemma_3 {n p : ℕ} (D : FastBestSubset.CDSS.Data n p) (hX : ∀ j, ∑ r, D.X r j ^ 2 = 1)
    (hlam0 : 0 < D.lam0) (hlam1 : 0 ≤ D.lam1) (hlam2 : 0 ≤ D.lam2) (β : Fin p → ℝ) :
    FastBestSubset.CDSS.IsCWMin D β ↔
      (∀ i ∈ FastBestSubset.CDSS.supp β,
          β i = Real.sign (FastBestSubset.CDSS.btilde D β i) * (|FastBestSubset.CDSS.btilde D β i| - D.lam1) / (1 + 2 * D.lam2) ∧
          D.lam1 < |FastBestSubset.CDSS.btilde D β i| ∧
          Real.sqrt (2 * D.lam0 / (1 + 2 * D.lam2)) ≤ |β i|) ∧
      (∀ i ∉ FastBestSubset.CDSS.supp β,
          (|FastBestSubset.CDSS.btilde D β i| - D.lam1) / (1 + 2 * D.lam2) ≤ Real.sqrt (2 * D.lam0 / (1 + 2 * D.lam2))) := by sorry

end FastBestSubset.PSI
