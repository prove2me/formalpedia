-- Prove2me | Theorems.Thm_FastBestSubset_CDSS_lemma_2
-- name    : FastBestSubset.CDSS.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:03:19.455718+00:00
-- url     : https://prove2.me/theorems/2b55f219-8c91-4657-90a9-6aabef98f812
-- title:
--   Lemma 2 — the set-valued thresholding operator T̃ (7) in closed form
-- statement:
--   Let $\lambda_0>0$, $\lambda_1,\lambda_2\ge0$ and $a\in\mathbb R$, and let $\tilde T(a,\lambda_0,\lambda_1,\lambda_2)$ be the set of minimizers over $u\in\mathbb R$ of
--   $$g(u)=\frac{1+2\lambda_2}{2}\Big(u-\frac{a}{1+2\lambda_2}\Big)^2+\lambda_1|u|+\lambda_0\mathbf 1[u\neq0].$$
--   Write $\tau=\frac{|a|-\lambda_1}{1+2\lambda_2}$ and $\theta=\sqrt{\frac{2\lambda_0}{1+2\lambda_2}}$. Then
--   $$\tilde T(a,\lambda_0,\lambda_1,\lambda_2)=\begin{cases}\{\mathrm{sign}(a)\,\tau\} & \text{if } \tau>\theta,\\ \{0\} & \text{if } \tau<\theta,\\ \{0,\ \mathrm{sign}(a)\,\tau\} & \text{if } \tau=\theta.\end{cases}$$
--
--   Applied with $a=\tilde\beta_i$, the lemma describes exactly which values of one coordinate minimize the objective with the others held fixed; the operator $T$ of (12) is a selection from it.
-- source:
--   Hazimeh, Mazumder, Fast Best Subset Selection: Coordinate Descent and Local Combinatorial Optimization Algorithms, arXiv:1803.01454v3, Lemma 2, p. 6 (proof §A.2, p. 36)

import Mathlib
import Definitions.Def_FastBestSubset_CDSS_Setting

open Filter Topology

namespace FastBestSubset.CDSS

/-- Lemma 2 (p. 6): the three cases of the set-valued thresholding operator `T̃` of (7). -/
theorem lemma_2 (a lam0 lam1 lam2 : ℝ) (hlam0 : 0 < lam0) (hlam1 : 0 ≤ lam1) (hlam2 : 0 ≤ lam2) :
    ((|a| - lam1) / (1 + 2 * lam2) > Real.sqrt (2 * lam0 / (1 + 2 * lam2)) →
        Ttilde a lam0 lam1 lam2 = {Real.sign a * (|a| - lam1) / (1 + 2 * lam2)}) ∧
    ((|a| - lam1) / (1 + 2 * lam2) < Real.sqrt (2 * lam0 / (1 + 2 * lam2)) →
        Ttilde a lam0 lam1 lam2 = {0}) ∧
    ((|a| - lam1) / (1 + 2 * lam2) = Real.sqrt (2 * lam0 / (1 + 2 * lam2)) →
        Ttilde a lam0 lam1 lam2 = {0, Real.sign a * (|a| - lam1) / (1 + 2 * lam2)}) := by sorry

end FastBestSubset.CDSS
