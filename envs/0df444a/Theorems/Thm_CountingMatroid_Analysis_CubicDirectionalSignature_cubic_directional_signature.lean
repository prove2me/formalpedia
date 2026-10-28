-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_CubicDirectionalSignature_cubic_directional_signature
-- name    : CountingMatroid.Analysis.CubicDirectionalSignature.cubic_directional_signature
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T16:12:41.57348+00:00
-- url     : https://prove2.me/theorems/df941e8a-0a72-44e7-b569-56ff2518111d
-- title:
--   One positive direction for nonnegative directional derivatives of a cubic
-- statement:
--   Let $\sigma$ be a finite variable set with decidable equality and let $p\in\mathbb Q[z_s:s\in\sigma]$ be homogeneous of degree three with nonnegative coefficients. Write $e_i$ for a unit exponent vector. The exchange condition on a set $S$ of finitely supported natural exponent vectors is: for all $x,y\in S$ and $i$ with $y_i<x_i$, some $j$ satisfies $x_j<y_j$ and $x-e_i+e_j\in S$. Assume this condition for the monomial support of $p$. For every $s$, suppose the real Hessian quadratic form of $\partial_s p$ has positive signature at most one, where positive signature means the maximum dimension of a positive-definite subspace. Then for every $d:\sigma\to\mathbb Q_{\ge0}$,
--
--   $$\operatorname{sig}_+\!\left(\operatorname{Hess}\left(\sum_s d_s\partial_s p\right)\right)\le1.$$
--
--   The Hessians are their constant matrices, viewed over $\mathbb R$. The compatibility supplied by one cubic and its exchange support is essential; this is not arbitrary-sum closure.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/CubicDirectionalSignature.lean#L48-L107

import Definitions.Def_CountingMatroid_Analysis_CubicTensorContraction
import Definitions.Def_CountingMatroid_Analysis_QuadraticNonpositiveHyperplane
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Multiset.Count
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Instances.Real.Lemmas

namespace CountingMatroid.Analysis.CubicDirectionalSignature
end CountingMatroid.Analysis.CubicDirectionalSignature
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
namespace CountingMatroid.Analysis.CubicThirdDerivativeSupport
end CountingMatroid.Analysis.CubicThirdDerivativeSupport
set_option autoImplicit false

/-!
The cubic step in directional Lorentzian closure. This isolates the spectral
obligation from support preservation: the constant Hessians of the coordinate
derivatives of a cubic arise from one symmetric nonnegative cubic tensor.
The polynomial support is identified with the tensor's unordered triples by
`CubicThirdDerivativeSupport`. The directional signature then follows from
the tensor contraction boundary in `CubicTensorContraction`, whose general
spectral proof remains open. No closure of arbitrary sums is asserted.
-/

namespace CountingMatroid.Analysis.CubicDirectionalSignature
end CountingMatroid.Analysis.CubicDirectionalSignature
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.CubicDirectionalSignature

open scoped BigOperators
open QuadraticNonpositiveHyperplane QuadraticSignatureHyperplane

theorem CountingMatroid.Analysis.CubicDirectionalSignature.cubic_directional_signature {σ : Type} [Fintype σ] [DecidableEq σ]
    (p : MvPolynomial σ ℚ) (hhom : p.IsHomogeneous 3)
    (hp : ∀ m, 0 ≤ p.coeff m)
    (hex : ∀ x ∈ p.support, ∀ y ∈ p.support, ∀ i, y i < x i →
      ∃ j, x j < y j ∧
        x - Finsupp.single i 1 + Finsupp.single j 1 ∈ p.support)
    (hsig : ∀ s, sigPos (Matrix.toQuadraticForm' (fun i j =>
      ((MvPolynomial.constantCoeff (MvPolynomial.pderiv i
        (MvPolynomial.pderiv j (MvPolynomial.pderiv s p))) : ℚ) : ℝ))) ≤ 1)
    (d : σ → ℚ) (hd : ∀ s, 0 ≤ d s) :
    sigPos (Matrix.toQuadraticForm' (fun i j =>
      ((MvPolynomial.constantCoeff (MvPolynomial.pderiv i (MvPolynomial.pderiv j
        (∑ s, MvPolynomial.C (d s) * MvPolynomial.pderiv s p))) : ℚ) : ℝ))) ≤ 1 := by sorry
