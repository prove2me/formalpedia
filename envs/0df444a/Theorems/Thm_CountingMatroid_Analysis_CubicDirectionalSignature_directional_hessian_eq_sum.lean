-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_CubicDirectionalSignature_directional_hessian_eq_sum
-- name    : CountingMatroid.Analysis.CubicDirectionalSignature.directional_hessian_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T14:47:02.418055+00:00
-- url     : https://prove2.me/theorems/720f1c3d-654a-48a6-a2f4-688c3f52adea
-- title:
--   The directional Hessian form is the weighted sum of coordinate Hessian forms
-- statement:
--   Let $I$ be a finite type with decidable equality, let $p\in\mathbb Q[x_i:i\in I]$ be any polynomial, and let $d:I\to\mathbb Q$ be any rational direction. Write $D_dp=\sum_s d_s\partial_sp$, and for any polynomial $f$ let $H_f(0)$ denote the matrix with entries $[1](\partial_i\partial_jf)$, its second derivatives evaluated at the origin. View these rational matrices as real matrices and put $Q_f(v)=v^{\mathsf T}H_f(0)v$. Then, as real quadratic forms,
--
--   $$Q_{D_dp}=\sum_{s\in I}d_sQ_{\partial_sp}.$$
--
--   This is a linearity identity. It imposes no homogeneity, cubic-degree, coefficient-sign, or direction-sign restriction.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/CubicDirectionalSignature.lean#L24-L46

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

set_option backward.isDefEq.respectTransparency false in

theorem CountingMatroid.Analysis.CubicDirectionalSignature.directional_hessian_eq_sum {σ : Type} [Fintype σ] [DecidableEq σ]
    (p : MvPolynomial σ ℚ) (d : σ → ℚ) :
    Matrix.toQuadraticForm' (fun i j =>
      ((MvPolynomial.constantCoeff (MvPolynomial.pderiv i (MvPolynomial.pderiv j
        (∑ s, MvPolynomial.C (d s) * MvPolynomial.pderiv s p))) : ℚ) : ℝ)) =
    ∑ s, (d s : ℝ) • Matrix.toQuadraticForm' (fun i j =>
      ((MvPolynomial.constantCoeff (MvPolynomial.pderiv i
        (MvPolynomial.pderiv j (MvPolynomial.pderiv s p))) : ℚ) : ℝ)) := by sorry
