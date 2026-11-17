-- Prove2me | Theorems.Thm_DetANN_HPIM_hpimTree_cost
-- name    : DetANN.HPIM.hpimTree_cost
-- status  : Proved
-- author  : @milia
-- created : 2026-11-16T06:36:46.930058+00:00
-- url     : https://prove2.me/theorems/28af0855-f1a6-4bca-a116-a206eff75eb1
-- title:
--   Query cost of the HPIM tree
-- statement:
--   There is an absolute constant $C_1$ such that the following holds. Let $m,N\ge1$, let $Y_1,\dots,Y_N\in\mathbb R^m$ be distinct, $\delta\in(0,1/2)$ and $q\in\mathbb R^m$. Then the search of $\mathrm{hpimTree}(Y,\delta)$ (definition `DetANN_HPIMTree`) has cost
--   $$\mathrm{cost}(q)\le C_1\,m\,\log^2(N/\delta).$$
--
--   The tree has at most $\lceil\log_2N\rceil+1$ levels, because each recursion at least halves the point set. Each level makes at most two lookups and one ladder search of $\lceil\log_2(M-1)\rceil=O(\log(N/\delta))$ probes, and each lookup visits $O(m\log(N/\delta))$ nodes.
-- source:
--   Original, written for the mission 'Deterministic Approximate Nearest Neighbors in High Dimensions' as part of a floor-free proof of DetANN.lemma_3_3 (Feng, Indyk, STOC 2027 submission, Lemma 3.3, p.7). The search tree follows Har-Peled, Indyk, Motwani, Approximate nearest neighbor: towards removing the curse of dimensionality, Theory of Computing 8 (2012), §2, made deterministic and floor-free.

import Mathlib
import Definitions.Def_DetANN_HPIMTree

namespace DetANN.HPIM

/-- **Query cost of the HPIM tree.** There is an absolute constant `C₁` such that for `m ≥ 1`, `N ≥ 1`
distinct points `Y ⊆ ℝ^m`, `δ ∈ (0, 1/2)` and every query `q`, the search of `hpimTree Y δ` visits at
most `C₁ m log²(N/δ)` nodes. -/
theorem hpimTree_cost :
    ∃ C₁ : ℕ, ∀ (m N : ℕ), 1 ≤ m → 1 ≤ N →
      ∀ Y : Fin N → EuclideanSpace ℝ (Fin m), Function.Injective Y →
        ∀ δ : ℝ, 0 < δ → δ < 1 / 2 → ∀ q : EuclideanSpace ℝ (Fin m),
          ((hpimTree Y δ).cost q : ℝ) ≤ C₁ * m * Real.log (N / δ) ^ 2 := by sorry

end DetANN.HPIM
