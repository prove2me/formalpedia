-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_CubicTensorRayleighContraction_cubic_tensor_rayleigh_contraction
-- name    : CountingMatroid.Analysis.CubicTensorRayleighContraction.cubic_tensor_rayleigh_contraction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T16:09:23.770407+00:00
-- url     : https://prove2.me/theorems/0f2ddba0-2b23-4e7e-be73-1784658c47a9
-- title:
--   Rayleigh inequalities imply cubic contraction closure
-- statement:
--   Let $\sigma$ be a finite index set with decidable equality and $T:\sigma^3\to\mathbb Q$ a nonnegative tensor satisfying $T_{sij}=T_{isj}=T_{sji}$. Define the real slice forms $Q_s(x)=\sum_{i,j}T_{sij}x_ix_j$ and their symmetric bilinear forms $B_s(x,y)=\sum_{i,j}T_{sij}x_i y_j$. Assume every cut $U\subseteq\sigma$ with active first indices on both sides has a nonzero entry $T_{sij}$ with $i\in U$ and $j\notin U$. Suppose also that for all $s$ and real vectors $e,v$,
--   $$Q_s(e)>0\quad\Longrightarrow\quad Q_s(v)Q_s(e)\le B_s(e,v)^2.$$
--   Then, for every nonnegative rational vector $d$, some real linear functional $\ell$ satisfies
--
--   $$\ell(v)=0\quad\Longrightarrow\quad\sum_s d_sQ_s(v)\le0.$$
--
--   This supplies the analytic contraction step from connected support and slice inequalities. The formal real scalar structure includes the standard inverse of $2$.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/CubicTensorRayleighContraction.lean#L22-L181

import Definitions.Def_CountingMatroid_Analysis_QuadraticNonpositiveHyperplane
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Instances.Real.Lemmas

namespace CountingMatroid.Analysis.CubicTensorRayleighContraction
end CountingMatroid.Analysis.CubicTensorRayleighContraction
namespace CountingMatroid.Analysis.NonnegativeContractionLimit
end CountingMatroid.Analysis.NonnegativeContractionLimit
namespace CountingMatroid.Analysis.QuadraticHyperplanePointwiseLimit
end CountingMatroid.Analysis.QuadraticHyperplanePointwiseLimit
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
The analytic local-to-global step for a symmetric nonnegative cubic tensor.
Its combinatorial input is expressed as connectivity across every cut of
active coordinates, independently of the exchange-support proof. Positive
contractions inherit this connectivity, and the slice reverse inequalities
supply the divided Rayleigh bound for the connected spectral theorem.
The contraction-limit theorem extends the result to zero coordinates.
-/

namespace CountingMatroid.Analysis.CubicTensorRayleighContraction
end CountingMatroid.Analysis.CubicTensorRayleighContraction
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.CubicTensorRayleighContraction

open scoped BigOperators
open QuadraticNonpositiveHyperplane

theorem CountingMatroid.Analysis.CubicTensorRayleighContraction.cubic_tensor_rayleigh_contraction {σ : Type} [Fintype σ] [DecidableEq σ]
    [Invertible (2 : ℝ)]
    (T : σ → σ → σ → ℚ) (hT : ∀ s i j, 0 ≤ T s i j)
    (hswap : ∀ s i j, T s i j = T i s j)
    (hlast : ∀ s i j, T s i j = T s j i)
    (hcross : ∀ U : Set σ,
      (∃ s i j, T s i j ≠ 0 ∧ s ∈ U) →
      (∃ s i j, T s i j ≠ 0 ∧ s ∉ U) →
      ∃ s i j, T s i j ≠ 0 ∧ i ∈ U ∧ j ∉ U)
    (hreverse : ∀ (s : σ) (e v : σ → ℝ),
      0 < Matrix.toQuadraticForm' (fun i j => (T s i j : ℝ)) e →
      Matrix.toQuadraticForm' (fun i j => (T s i j : ℝ)) v *
        Matrix.toQuadraticForm' (fun i j => (T s i j : ℝ)) e ≤
      ((Matrix.toQuadraticForm' (fun i j => (T s i j : ℝ))).associated e v) ^ 2)
    (d : σ → ℚ) (hd : ∀ s, 0 ≤ d s) :
    HasNonpositiveHyperplane (∑ s, (d s : ℝ) •
      Matrix.toQuadraticForm' (fun i j => (T s i j : ℝ))) := by sorry
