-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_CubicTensorContraction_cubic_tensor_contraction_hyperplane
-- name    : CountingMatroid.Analysis.CubicTensorContraction.cubic_tensor_contraction_hyperplane
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T16:11:03.454238+00:00
-- url     : https://prove2.me/theorems/6d1ed4f1-4acf-48ba-a75c-e83443a54393
-- title:
--   Nonnegative contraction of compatible cubic slices has a nonpositive kernel
-- statement:
--   Let $\sigma$ be a finite index set with decidable equality and $T:\sigma^3\to\mathbb Q$ a nonnegative tensor satisfying $T_{sij}=T_{isj}=T_{sji}$. Define the real slice forms $Q_s(x)=\sum_{i,j}T_{sij}x_ix_j$ and their symmetric bilinear forms $B_s(x,y)=\sum_{i,j}T_{sij}x_i y_j$.
--
--   Write $e_i$ for a unit exponent vector. The exchange condition on a set $S$ of finitely supported natural exponent vectors is: for all $x,y\in S$ and $i$ with $y_i<x_i$, some $j$ satisfies $x_j<y_j$ and $x-e_i+e_j\in S$. Assume exchange for $S=\{e_i+e_j+e_s:T_{sij}\ne0\}$. Suppose each $Q_s$ is nonpositive on the kernel of some real linear functional. For every nonnegative rational vector $d$, there exists a real linear functional $\ell$ such that
--
--   $$\ell(x)=0\quad\Longrightarrow\quad\sum_s d_sQ_s(x)\le0.$$
--
--   The kernel has codimension at most one; the functional may be zero. The theorem is a compatible-tensor closure statement.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/CubicTensorContraction.lean#L37-L108

import Definitions.Def_CountingMatroid_Analysis_CubicTensorContraction
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
namespace CountingMatroid.Analysis.CubicExchangeCut
end CountingMatroid.Analysis.CubicExchangeCut
set_option autoImplicit false

/-!
The spectral part of cubic directional closure, stated independently of
polynomial calculus. A symmetric nonnegative tensor carries the exchange
support of a homogeneous cubic. The coordinate slices have at most one
positive direction; the remaining obligation is to propagate that bound to
every nonnegative contraction. Arbitrary sums of such slices have no such
closure property without the tensor and support hypotheses.

The remaining obligation is the degree-three instance of the nonnegative
directional-derivative closure cited in the paper. Brändén–Huh, Corollary
2.11, states this closure for the recursively defined classes of polynomials
with M-convex support and Lorentzian quadratic derivatives. The proof here
separates the proved exchange-to-connectivity argument from the analytic
Rayleigh contraction lemma, whose normalized spectral and boundary steps
remain open. The parent reduction does not assume an aggregate signature
bound or alter the theorem hypotheses.
-/

namespace CountingMatroid.Analysis.CubicTensorContraction
end CountingMatroid.Analysis.CubicTensorContraction
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.CubicTensorContraction

open scoped BigOperators
open QuadraticNonpositiveHyperplane

theorem CountingMatroid.Analysis.CubicTensorContraction.cubic_tensor_contraction_hyperplane {σ : Type} [Fintype σ] [DecidableEq σ]
    (T : σ → σ → σ → ℚ) (hT : ∀ s i j, 0 ≤ T s i j)
    (hswap : ∀ s i j, T s i j = T i s j)
    (hlast : ∀ s i j, T s i j = T s j i)
    (hex : ∀ x ∈ cubicTensorSupport T, ∀ y ∈ cubicTensorSupport T,
      ∀ i, y i < x i → ∃ j, x j < y j ∧
        x - Finsupp.single i 1 + Finsupp.single j 1 ∈ cubicTensorSupport T)
    (hslice : ∀ s, HasNonpositiveHyperplane
      (Matrix.toQuadraticForm' (fun i j => (T s i j : ℝ))))
    (d : σ → ℚ) (hd : ∀ s, 0 ≤ d s) :
    HasNonpositiveHyperplane (∑ s, (d s : ℝ) •
      Matrix.toQuadraticForm' (fun i j => (T s i j : ℝ))) := by sorry
