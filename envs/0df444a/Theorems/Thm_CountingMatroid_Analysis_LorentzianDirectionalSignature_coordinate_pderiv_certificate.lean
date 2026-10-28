-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_LorentzianDirectionalSignature_coordinate_pderiv_certificate
-- name    : CountingMatroid.Analysis.LorentzianDirectionalSignature.coordinate_pderiv_certificate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T15:53:15.064777+00:00
-- url     : https://prove2.me/theorems/415c27b0-82d8-4a89-99c3-946a193807ad
-- title:
--   Coordinate differentiation preserves the coordinate Lorentzian certificate
-- statement:
--   For a finite variable set $\sigma$, write $D_d=\sum_{s\in\sigma}d_s\partial_s$ and let $H_f$ be the real matrix with entries $[1](\partial_s\partial_t f)$, where $[1]$ denotes constant coefficient. A coordinate Lorentzian certificate of degree $m$ for a rational polynomial $f$ means: $f$ is homogeneous of degree $m$; its coefficients are nonnegative; its support satisfies the exchange rule $x,y\in\operatorname{supp}(f)$ and $y_i<x_i\Rightarrow\exists j,\ x_j<y_j,\ x-e_i+e_j\in\operatorname{supp}(f)$; and, after any $m-2$ coordinate derivatives, the constant-Hessian quadratic form has positive index at most one. Here $e_i$ is the $i$th unit exponent, and positive index is the maximal dimension of a subspace on which the form is positive definite. The derivative condition ranges over lists of length $\ell$ satisfying $\ell+2=m$. If $p\in\mathbb Q[x_s:s\in\sigma]$ has a coordinate Lorentzian certificate of degree $n\in\mathbb N$, then, for every $s\in\sigma$, $$\partial_s p\text{ has a coordinate Lorentzian certificate of degree }\max(n-1,0).$$
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/LorentzianDirectionalSignature.lean#L76-L99

import Definitions.Def_CountingMatroid_Analysis_CubicTensorContraction
import Definitions.Def_CountingMatroid_Analysis_LorentzianDirectionalSignature
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
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
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
namespace CountingMatroid.Analysis.NonnegativeDirectionalMConvexSupport
end CountingMatroid.Analysis.NonnegativeDirectionalMConvexSupport
set_option autoImplicit false

/-!
Coordinate certificates for the Lorentzian argument record homogeneous degree,
nonnegative coefficients, M-convex support, and the positive-signature bound
for every quadratic coordinate derivative. The directional signature theorem
is reduced to two independent obligations: M-convex support preservation under
nonnegative directional differentiation, and the cubic signature mixing step.
The coefficient/support calculations and the reduction through coordinate and
directional derivative lists are implemented. The two imported obligations
remain open, so the general theorem is not yet a completed proof. The original
degree-two proof is preserved.

The paper invokes the Brändén–Huh closure results at main.tex:340-348. The pinned
libraries contain homogeneous partial-derivative and quadratic-signature APIs,
but no applicable Lorentzian or M-convex directional-closure theorem was found.

-/

namespace CountingMatroid.Analysis.LorentzianDirectionalSignature
end CountingMatroid.Analysis.LorentzianDirectionalSignature
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.LorentzianDirectionalSignature

open scoped BigOperators

theorem CountingMatroid.Analysis.LorentzianDirectionalSignature.coordinate_pderiv_certificate {σ : Type} [Fintype σ]
    (p : MvPolynomial σ ℚ) (n : ℕ) (hp : CoordinateLorentzian p n) (s : σ) :
    CoordinateLorentzian (MvPolynomial.pderiv s p) (n - 1) := by sorry
