-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_ConnectedNormalizedRayleigh_connected_normalized_rayleigh
-- name    : CountingMatroid.Analysis.ConnectedNormalizedRayleigh.connected_normalized_rayleigh
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T15:53:03.232002+00:00
-- url     : https://prove2.me/theorems/b8984094-2e2e-4639-87fb-19f1c80289e4
-- title:
--   A connected normalized Rayleigh bound gives a nonpositive kernel
-- statement:
--   Let $I$ be a finite type with decidable equality and let $C$ be a symmetric real matrix with nonnegative entries. Call $i$ active if some $C_{ij}$ is nonzero. Assume that every subset $U\subseteq I$ containing an active index and having an active index outside it has a nonzero crossing entry: there are $i\in U$ and $j\notin U$ with $C_{ij}\ne0$. Write $r_i=\sum_jC_{ij}$. Zero rows are allowed.
--
--   Suppose that every $v\in\mathbb R^I$ satisfies
--
--   $$v^{\mathsf T}Cv\le\sum_i\frac{(Cv)_i^2}{r_i},$$
--
--   where division by zero is defined to be zero. Then there exists a real linear functional $\ell:\mathbb R^I\to\mathbb R$ such that
--
--   $$\ell(v)=0\quad\Longrightarrow\quad v^{\mathsf T}Cv\le0.$$
--
--   Thus the quadratic form is nonpositive on a linear subspace of codimension at most one. The functional is permitted to be zero.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/ConnectedNormalizedRayleigh.lean#L13-L130

import Definitions.Def_CountingMatroid_Analysis_QuadraticNonpositiveHyperplane
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.Tactic

namespace CountingMatroid.Analysis.ConnectedNormalizedRayleigh
end CountingMatroid.Analysis.ConnectedNormalizedRayleigh
namespace CountingMatroid.Analysis.ConnectedLaplacianKernel
end CountingMatroid.Analysis.ConnectedLaplacianKernel
namespace CountingMatroid.Analysis.RayleighFixedKernel
end CountingMatroid.Analysis.RayleighFixedKernel
set_option autoImplicit false

namespace CountingMatroid.Analysis.ConnectedNormalizedRayleigh
end CountingMatroid.Analysis.ConnectedNormalizedRayleigh
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ConnectedNormalizedRayleigh

open scoped BigOperators ComplexOrder
open QuadraticNonpositiveHyperplane

theorem CountingMatroid.Analysis.ConnectedNormalizedRayleigh.connected_normalized_rayleigh {σ : Type} [Fintype σ] [DecidableEq σ]
    (C : Matrix σ σ ℝ) (hC : ∀ i j, 0 ≤ C i j)
    (hsym : ∀ i j, C i j = C j i)
    (hcross : ∀ U : Set σ,
      (∃ i j, C i j ≠ 0 ∧ i ∈ U) →
      (∃ i j, C i j ≠ 0 ∧ i ∉ U) →
      ∃ i j, C i j ≠ 0 ∧ i ∈ U ∧ j ∉ U)
    (hbound : ∀ v : σ → ℝ, (∑ i, v i * C.mulVec v i) ≤
      ∑ i, (C.mulVec v i)^2 / (∑ j, C i j)) :
    HasNonpositiveHyperplane C.toQuadraticForm' := by sorry
