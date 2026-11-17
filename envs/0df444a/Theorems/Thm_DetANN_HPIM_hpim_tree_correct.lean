-- Prove2me | Theorems.Thm_DetANN_HPIM_hpim_tree_correct
-- name    : DetANN.HPIM.hpim_tree_correct
-- status  : Proved
-- author  : @milia
-- created : 2026-11-16T06:36:58.221858+00:00
-- url     : https://prove2.me/theorems/cd2d3045-171d-40c4-9e0c-f1fdae28c0fe
-- title:
--   The HPIM tree is a (1+δ)-ANN structure
-- statement:
--   There is an absolute constant $C_1$ such that the following holds. Let $m,N\ge1$, let $Y_1,\dots,Y_N\in\mathbb R^m$ be distinct, $\delta\in(0,1/2)$ and $q\in\mathbb R^m$. The search of $\mathrm{hpimTree}(Y,\delta)$ (definition `DetANN_HPIMTree`) returns an index $k$ with
--   $$\|q-Y_k\|\le(1+\delta)\,\|q-Y_j\|\qquad\text{for all }j,$$
--   and its cost is at most $C_1\,m\,\log^2(N/\delta)$.
--
--   This is the mathematical content of `DetANN.lemma_3_3`. The remaining steps are the two machine programs: one builds the tree in memory, and one runs this search.
-- source:
--   Original, written for the mission 'Deterministic Approximate Nearest Neighbors in High Dimensions' as part of a floor-free proof of DetANN.lemma_3_3 (Feng, Indyk, STOC 2027 submission, Lemma 3.3, p.7). The search tree follows Har-Peled, Indyk, Motwani, Approximate nearest neighbor: towards removing the curse of dimensionality, Theory of Computing 8 (2012), §2, made deterministic and floor-free.

import Mathlib
import Definitions.Def_DetANN_HPIMTree

namespace DetANN.HPIM

/-- **The HPIM tree is a `(1+δ)`-ANN structure with query cost `O(m log²(N/δ))`.** There is an absolute
constant `C₁` such that for `m ≥ 1`, `N ≥ 1` distinct points `Y ⊆ ℝ^m`, `δ ∈ (0, 1/2)` and every query
`q`, the search of `hpimTree Y δ` returns an index `k` with `‖q − Y_k‖ ≤ (1 + δ) ‖q − Y_j‖` for all
`j`, and visits at most `C₁ m log²(N/δ)` nodes. -/
theorem hpim_tree_correct :
    ∃ C₁ : ℕ, ∀ (m N : ℕ), 1 ≤ m → 1 ≤ N →
      ∀ Y : Fin N → EuclideanSpace ℝ (Fin m), Function.Injective Y →
        ∀ δ : ℝ, 0 < δ → δ < 1 / 2 → ∀ q : EuclideanSpace ℝ (Fin m),
          (∃ k : Fin N, (hpimTree Y δ).search q = k ∧ ∀ j : Fin N, ‖q - Y k‖ ≤ (1 + δ) * ‖q - Y j‖) ∧
          ((hpimTree Y δ).cost q : ℝ) ≤ C₁ * m * Real.log (N / δ) ^ 2 := by sorry

end DetANN.HPIM
