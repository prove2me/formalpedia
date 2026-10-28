-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_ConnectedRayleighHyperplane_connected_rayleigh_hyperplane
-- name    : CountingMatroid.Analysis.ConnectedRayleighHyperplane.connected_rayleigh_hyperplane
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T15:54:04.45144+00:00
-- url     : https://prove2.me/theorems/aa65da7d-ff0c-4f29-88af-c0b6c9a4e8f6
-- title:
--   Positive diagonal scaling converts a weighted Rayleigh bound to a nonpositive kernel
-- statement:
--   Let $I$ be a finite type with decidable equality and let $A$ be a symmetric real matrix with nonnegative entries. Assume that every set $U\subseteq I$ containing an index incident to a nonzero entry and having such an index outside $U$ admits $i\in U$, $j\notin U$ with $A_{ij}\ne0$. Let $w\in\mathbb R^I$ be strictly positive at every coordinate. If every $v\in\mathbb R^I$ satisfies
--
--   $$v^{\mathsf T}Av\le\sum_i\frac{w_i(Av)_i^2}{(Aw)_i},$$
--
--   then there is a real linear functional $\ell$ such that
--
--   $$\ell(v)=0\quad\Longrightarrow\quad v^{\mathsf T}Av\le0.$$
--
--   Division by zero is interpreted as zero. Zero rows are allowed, and the kernel may have codimension zero. The formal statement also carries the automatic real-field invertibility instance for $2$.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/ConnectedRayleighHyperplane.lean#L20-L103

import Definitions.Def_CountingMatroid_Analysis_QuadraticNonpositiveHyperplane
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.Tactic

namespace CountingMatroid.Analysis.ConnectedRayleighHyperplane
end CountingMatroid.Analysis.ConnectedRayleighHyperplane
namespace CountingMatroid.Analysis.ConnectedNormalizedRayleigh
end CountingMatroid.Analysis.ConnectedNormalizedRayleigh
namespace CountingMatroid.Analysis.ConnectedLaplacianKernel
end CountingMatroid.Analysis.ConnectedLaplacianKernel
namespace CountingMatroid.Analysis.RayleighFixedKernel
end CountingMatroid.Analysis.RayleighFixedKernel
namespace CountingMatroid.Analysis.QuadraticSignatureHyperplane
end CountingMatroid.Analysis.QuadraticSignatureHyperplane
set_option autoImplicit false

/-!
A matrix formulation of the spectral step in cubic contraction. The weighted
Rayleigh inequality excludes normalized eigenvalues strictly between zero and
one. Connected nonnegative support must then make the eigenvalue one simple.
Zero rows are handled by assigning them unit weight in the auxiliary inner
product; the resulting hyperplane is transported by positive diagonal scaling.
-/

namespace CountingMatroid.Analysis.ConnectedRayleighHyperplane
end CountingMatroid.Analysis.ConnectedRayleighHyperplane
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ConnectedRayleighHyperplane

open scoped BigOperators
open QuadraticNonpositiveHyperplane

theorem CountingMatroid.Analysis.ConnectedRayleighHyperplane.connected_rayleigh_hyperplane {σ : Type} [Fintype σ] [DecidableEq σ]
    [Invertible (2 : ℝ)] (A : Matrix σ σ ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (hsym : ∀ i j, A i j = A j i)
    (hcross : ∀ U : Set σ,
      (∃ i j, A i j ≠ 0 ∧ i ∈ U) →
      (∃ i j, A i j ≠ 0 ∧ i ∉ U) →
      ∃ i j, A i j ≠ 0 ∧ i ∈ U ∧ j ∉ U)
    (w : σ → ℝ) (hw : ∀ i, 0 < w i)
    (hbound : ∀ v : σ → ℝ, Matrix.toQuadraticForm' A v ≤
      ∑ i, w i * (A.mulVec v i) ^ 2 / A.mulVec w i) :
    HasNonpositiveHyperplane (Matrix.toQuadraticForm' A) := by sorry
