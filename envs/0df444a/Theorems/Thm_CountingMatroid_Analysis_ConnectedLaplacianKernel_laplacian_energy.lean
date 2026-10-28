-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_ConnectedLaplacianKernel_laplacian_energy
-- name    : CountingMatroid.Analysis.ConnectedLaplacianKernel.laplacian_energy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T14:46:58.486631+00:00
-- url     : https://prove2.me/theorems/a708d48d-f3aa-4e57-b16a-b3fd4137570a
-- title:
--   Symmetric Laplacian energy identity
-- statement:
--   Let $I$ be a finite type, let $C=(C_{ij})_{i,j\in I}$ be a symmetric real matrix, and let $x\in\mathbb R^I$. Put $r_i=\sum_jC_{ij}$. Then
--
--   $$\sum_i r_ix_i^2-\sum_i x_i(Cx)_i=\frac12\sum_{i,j}C_{ij}(x_i-x_j)^2.$$
--
--   No nonnegativity hypothesis on the entries is needed for this identity. When entries are nonnegative, it exhibits the Laplacian form as a nonnegative edge energy.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/ConnectedLaplacianKernel.lean#L11-L35

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

theorem CountingMatroid.Analysis.ConnectedLaplacianKernel.laplacian_energy {σ : Type} [Fintype σ] (C : Matrix σ σ ℝ)
    (hsym : ∀ i j, C i j = C j i) (x : σ → ℝ) :
    (∑ i, (∑ j, C i j) * (x i)^2) - (∑ i, x i * C.mulVec x i) =
      (∑ i, ∑ j, C i j * (x i - x j)^2) / 2 := by sorry
