-- Prove2me | Theorems.Thm_CompOT_Auction_eq_3_8
-- name    : CompOT.Auction.eq_3_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:14:01.456443+00:00
-- url     : https://prove2.me/theorems/0d9ef10f-6fd5-4029-981a-bc136d7af2d6
-- title:
--   (3.8), p. 419 — exact complementary slackness makes σ an optimal assignment and (g^{C̄}, g) an optimal dual pair
-- statement:
--   Let $\mathbf C\in\mathbb R^{n\times n}$ be a cost matrix, $\mathbf g\in\mathbb R^n$ a dual vector and $\sigma$ a permutation of $[\![n]\!]$ such that, for every $i$,
--   $$
--   \mathbf C_{i,\sigma_i}-\mathbf g_{\sigma_i}=\min_j \mathbf C_{i,j}-\mathbf g_j. \tag{3.8}
--   $$
--   Then both are optimal:
--
--   1. $\sigma$ is an optimal assignment: $\sum_i \mathbf C_{i,\sigma_i}\le\sum_i \mathbf C_{i,\tau_i}$ for every permutation $\tau$;
--   2. $(\mathbf g^{\bar{\mathbf C}},\mathbf g)$, where $(\mathbf g^{\bar{\mathbf C}})_i=\min_j\mathbf C_{i,j}-\mathbf g_j$, is dual feasible, $\mathbf g^{\bar{\mathbf C}}_i+\mathbf g_j\le\mathbf C_{i,j}$ for all $i,j$;
--   3. and it is an optimal dual pair: $\sum_i\mathbf f'_i+\sum_j\mathbf g'_j\le\sum_i(\mathbf g^{\bar{\mathbf C}})_i+\sum_j\mathbf g_j$ for every dual feasible $(\mathbf f',\mathbf g')$.
--
--   This is the exact form of the complementary slackness condition that the auction algorithm relaxes to ε-complementary slackness.
--
--   **Formalization Note** $[\![n]\!]$ is `Fin n`. The optimal assignment problem (2.2) and its dual (2.20) with uniform marginals $a=b=\mathbb 1_n/n$ carry a factor $\frac1n$ in both objectives; it is dropped here, which does not change which assignments or dual pairs are optimal.
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), §3.7, (3.8), p. 419

import Mathlib
import Definitions.Def_CompOT_Auction_Defs

namespace CompOT.Auction

/-- (3.8), p. 419: if a dual vector `g` and a permutation `σ` satisfy
`C_{i,σ_i} − g_{σ_i} = min_j C_{i,j} − g_j` for every `i`, then `σ` is an optimal assignment and
`(g^{C̄}, g)` is an optimal dual pair. -/
theorem eq_3_8 {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (g : Fin n → ℝ)
    (σ : Equiv.Perm (Fin n)) (h : ∀ i, C i (σ i) - g (σ i) = ⨅ j, (C i j - g j)) :
    (∀ τ : Equiv.Perm (Fin n), assignmentCost C σ ≤ assignmentCost C τ) ∧
      DualFeasible C (cbarTransform C g) g ∧
      ∀ f' g' : Fin n → ℝ, DualFeasible C f' g' →
        ∑ i, f' i + ∑ j, g' j ≤ ∑ i, cbarTransform C g i + ∑ j, g j := by sorry

end CompOT.Auction
