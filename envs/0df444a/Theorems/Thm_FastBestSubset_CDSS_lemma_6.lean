-- Prove2me | Theorems.Thm_FastBestSubset_CDSS_lemma_6
-- name    : FastBestSubset.CDSS.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:03:14.437577+00:00
-- url     : https://prove2.me/theorems/7f46847b-5ab7-460a-afca-90e7cfe5d8c8
-- title:
--   Lemma 6 — for the (L0) and (L0L1) problems, ‖βᵏ‖₀ ≤ min{n, p} for all k
-- statement:
--   Consider Problem (2) with $\lambda_2=0$, that is, the (L0) problem ($\lambda_1=0$) or the (L0L1) problem ($\lambda_1>0$), with $\lambda_0>0$ and columns of $X$ of unit norm. Assume that every $\min\{n,p\}$ columns of $X$ are linearly independent (Assumption 1) and, when $p>n$, that the initial point satisfies Assumption 2. Let $\{\beta^k\}$ be the iterates of Algorithm 1 with a positive integer $C$. Then
--   $$\|\beta^k\|_0\le\min\{n,p\}\qquad\text{for all }k .$$
--
--   The bound on the support size is what makes the least-squares part strongly convex on every support visited, which drives the boundedness and uniqueness arguments that follow.
-- source:
--   Hazimeh, Mazumder, Fast Best Subset Selection: Coordinate Descent and Local Combinatorial Optimization Algorithms, arXiv:1803.01454v3, Lemma 6, p. 12 (proof §A.5, p. 37)

import Mathlib
import Definitions.Def_FastBestSubset_CDSS_Setting

open Filter Topology

namespace FastBestSubset.CDSS

/-- Lemma 6 (p. 12): for the (L0) and (L0L1) problems (`λ₂ = 0`), under Assumptions 1–2,
`‖βᵏ‖₀ ≤ min{n, p}` for all `k`. -/
theorem lemma_6 {n p : ℕ} [NeZero p] (D : Data n p) (hX : ∀ j, ∑ r, D.X r j ^ 2 = 1)
    (hlam0 : 0 < D.lam0) (hlam1 : 0 ≤ D.lam1) (hlam2 : D.lam2 = 0)
    (C : ℕ) (hC : 0 < C) (β0 : Fin p → ℝ)
    (hA1 : Assumption1 D) (hA2 : n < p → Assumption2 D β0) :
    ∀ k, l0 (iter D C β0 k) ≤ min n p := by sorry

end FastBestSubset.CDSS
