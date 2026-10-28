-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_ConnectedLaplacianKernel_connected_laplacian_kernel
-- name    : CountingMatroid.Analysis.ConnectedLaplacianKernel.connected_laplacian_kernel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T15:27:58.521595+00:00
-- url     : https://prove2.me/theorems/b88c5104-e991-4025-b636-7b7d0cbeac33
-- title:
--   A connected Laplacian fixed vector with zero weighted mean has zero image
-- statement:
--   Let $I$ be a finite type with decidable equality and let $C$ be a symmetric real matrix with nonnegative entries. Call $i$ active if some $C_{ij}$ is nonzero. Assume that every subset $U\subseteq I$ containing an active index and having an active index outside it has a nonzero crossing entry: there are $i\in U$ and $j\notin U$ with $C_{ij}\ne0$. Write $r_i=\sum_jC_{ij}$. Zero rows are allowed.
--
--   For any vector $x\in\mathbb R^I$ satisfying
--
--   $$(Cx)_i=r_ix_i\quad\text{for every }i,\qquad \sum_i r_ix_i=0,$$
--
--   one has
--
--   $$Cx=0.$$
--
--   The conclusion is about the matrix image; coordinates in zero rows need not themselves vanish.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/ConnectedLaplacianKernel.lean#L37-L104

import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Tactic

namespace CountingMatroid.Analysis.ConnectedLaplacianKernel
end CountingMatroid.Analysis.ConnectedLaplacianKernel
set_option autoImplicit false

namespace CountingMatroid.Analysis.ConnectedLaplacianKernel
end CountingMatroid.Analysis.ConnectedLaplacianKernel
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ConnectedLaplacianKernel

open scoped BigOperators

theorem CountingMatroid.Analysis.ConnectedLaplacianKernel.connected_laplacian_kernel {σ : Type} [Fintype σ] [DecidableEq σ]
    (C : Matrix σ σ ℝ) (hC : ∀ i j, 0 ≤ C i j)
    (hsym : ∀ i j, C i j = C j i)
    (hcross : ∀ U : Set σ,
      (∃ i j, C i j ≠ 0 ∧ i ∈ U) →
      (∃ i j, C i j ≠ 0 ∧ i ∉ U) →
      ∃ i j, C i j ≠ 0 ∧ i ∈ U ∧ j ∉ U)
    (x : σ → ℝ)
    (hfixed : ∀ i, C.mulVec x i = (∑ j, C i j) * x i)
    (hmean : ∑ i, (∑ j, C i j) * x i = 0) : C.mulVec x = 0 := by sorry
