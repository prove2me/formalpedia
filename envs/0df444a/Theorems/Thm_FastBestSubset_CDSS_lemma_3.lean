-- Prove2me | Theorems.Thm_FastBestSubset_CDSS_lemma_3
-- name    : FastBestSubset.CDSS.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:03:42.198961+00:00
-- url     : https://prove2.me/theorems/49f395d8-b4ee-4d54-84d6-66eda759982b
-- title:
--   Lemma 3 — characterization (8) of CW minima of Problem (2)
-- statement:
--   Let $X$ have unit-norm columns, $\lambda_0>0$ and $\lambda_1,\lambda_2\ge0$. A vector $\beta\in\mathbb R^p$ is a CW minimum of Problem (2) if and only if, with $\tilde\beta_i=\langle y-\sum_{j\ne i}X_j\beta_j,X_i\rangle$,
--   $$\beta_i=\mathrm{sign}(\tilde\beta_i)\frac{|\tilde\beta_i|-\lambda_1}{1+2\lambda_2},\quad |\tilde\beta_i|>\lambda_1\quad\text{and}\quad|\beta_i|\ge\sqrt{\frac{2\lambda_0}{1+2\lambda_2}}\qquad\text{for every } i\in\mathrm{Supp}(\beta),$$
--   $$\frac{|\tilde\beta_i|-\lambda_1}{1+2\lambda_2}\le\sqrt{\frac{2\lambda_0}{1+2\lambda_2}}\qquad\text{for every } i\notin\mathrm{Supp}(\beta).$$
--
--   Comparing with (5), every CW minimum is a stationary solution. The characterization is how the limit of Algorithm 1 is recognized as a CW minimum at the end of the proof of Theorem 2.
--
--   **Formalization Note** The printed condition (8) on p. 7 omits $|\tilde\beta_i|>\lambda_1$ on the support. Without it the "if" direction fails when $\lambda_1>0$: for $p=1$, $X=1$, $y=0.1$, $\lambda_1=10$, $\lambda_2=0$ and small $\lambda_0$, the vector $\beta=-9.9$ satisfies the printed conditions but is not a coordinate-wise minimizer. The condition is the one in the stationarity characterization (5), which (8) refines, and it follows from Lemma 2 for any genuine CW minimum. $\mathrm{sign}$ is `Real.sign`.
-- source:
--   Hazimeh, Mazumder, Fast Best Subset Selection: Coordinate Descent and Local Combinatorial Optimization Algorithms, arXiv:1803.01454v3, Lemma 3, (8), p. 7 (with the condition |β̃ᵢ| > λ₁ of (5), p. 6)

import Mathlib
import Definitions.Def_FastBestSubset_CDSS_Setting

open Filter Topology

namespace FastBestSubset.CDSS

/-- Lemma 3 (p. 7), with the condition `|β̃ᵢ| > λ₁` of (5) on the support (see the
natural-language statement): `β` is a CW minimum iff (8) holds. -/
theorem lemma_3 {n p : ℕ} (D : Data n p) (hX : ∀ j, ∑ r, D.X r j ^ 2 = 1)
    (hlam0 : 0 < D.lam0) (hlam1 : 0 ≤ D.lam1) (hlam2 : 0 ≤ D.lam2) (β : Fin p → ℝ) :
    IsCWMin D β ↔
      (∀ i ∈ supp β,
          β i = Real.sign (btilde D β i) * (|btilde D β i| - D.lam1) / (1 + 2 * D.lam2) ∧
          D.lam1 < |btilde D β i| ∧
          Real.sqrt (2 * D.lam0 / (1 + 2 * D.lam2)) ≤ |β i|) ∧
      (∀ i ∉ supp β,
          (|btilde D β i| - D.lam1) / (1 + 2 * D.lam2) ≤ Real.sqrt (2 * D.lam0 / (1 + 2 * D.lam2))) := by sorry

end FastBestSubset.CDSS
