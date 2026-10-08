-- Prove2me | Theorems.Thm_BSUMConv_BSUM_limit_block_minimizes
-- name    : BSUMConv.BSUM.limit_block_minimizes
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:26:02.69671+00:00
-- url     : https://prove2.me/theorems/033e59e9-a476-4e8f-a646-acc7f07dc87c
-- title:
--   Proof of Theorem 2(a), p. 12 — at a limit point z, z_k minimises u_k(·, z) over X_k for every block k
-- statement:
--   In the setting of Theorem 2(a) (closed convex blocks, $f$ continuous on $\mathcal X$, Assumption 2, quasi-convexity of $u_i$ in $x_i$, unique block minimisers, cyclic BSUM iterates $x^r$), let $z$ be a limit point of $(x^r)$. Then for every block $k$,
--
--   $$u_k(z_k,z)\ \le\ u_k(x_k,z)\qquad\forall\,x_k\in\mathcal X_k.$$
--
--   The paper writes the case $k=1$ and adds "similarly, by repeating the above argument for the other blocks"; the statement covers every block.
-- source:
--   Razaviyayn, Hong & Luo, arXiv:1209.2385v1, p. 12, proof of Theorem 2(a), u_1(z_1, z) ≤ u_1(x_1, z) ∀ x_1 ∈ X_1 and its repetition for the other blocks

import Mathlib
import Definitions.Def_TsengBCD_Stationary_Setting
import Definitions.Def_BSUMConv_BSUM_Setting

namespace BSUMConv.BSUM

open TsengBCD.Stationary Filter Topology

/-- Proof of Theorem 2(a), p. 12: under quasi-convexity of the `u_i` in `x_i` and uniqueness of
the block minimisers, at every limit point `z` of a cyclic BSUM run, `z_k` minimises
`u_k(·, z)` over `X_k` for every block `k`: `u_k(z_k, z) ≤ u_k(x_k, z)` for all `x_k ∈ X_k`. -/
theorem limit_block_minimizes {N : ℕ} {n : Fin N → ℕ}
    (Xs : (i : Fin N) → Set (EuclideanSpace ℝ (Fin (n i))))
    (hXconv : ∀ i, Convex ℝ (Xs i)) (hXclosed : ∀ i, IsClosed (Xs i))
    (f : X n → ℝ) (hf : ContinuousOn f (Xset Xs))
    (u : (i : Fin N) → EuclideanSpace ℝ (Fin (n i)) → X n → ℝ) (hA2 : Assumption2 Xs f u)
    (hqc : BlockQuasiconvex Xs u) (huniq : ∀ i, UniqueBlockMin Xs u i)
    (s : ℕ → Fin N) (hs : IsCyclic s) (x : ℕ → X n) (hx : IsBSUMRun Xs u s x)
    (z : X n) (hz : MapClusterPt z atTop x) :
    ∀ (k : Fin N), ∀ w ∈ Xs k, u k (z k) z ≤ u k w z := by sorry

end BSUMConv.BSUM
