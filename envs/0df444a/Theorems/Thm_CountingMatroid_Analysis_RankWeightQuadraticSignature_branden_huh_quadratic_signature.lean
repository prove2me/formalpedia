-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_RankWeightQuadraticSignature_branden_huh_quadratic_signature
-- name    : CountingMatroid.Analysis.RankWeightQuadraticSignature.branden_huh_quadratic_signature
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T16:17:20.316347+00:00
-- url     : https://prove2.me/theorems/0b23f77d-a1a4-4d3e-859b-7a7cf7b5926e
-- title:
--   Quadratic descendants of the rank-weight polynomial have signature at most one
-- statement:
--   Let $E$ be a finite set of size $d$, $N$ a matroid on $E$, and $r_N(A)$ the finite natural-number rank of $A\subseteq E$. Introduce a fresh homogenizing variable $z_0$, distinct from the variables $z_a$ for $a\in E$, and define $$P_{N,q}(z_0,z)=\sum_{A\subseteq E}(q^{r_N(A)})^{-1}z_0^{d-|A|}\prod_{a\in A}z_a.$$ Suppose $N$ has full ground $E$ and rational $0<q\le1$. Let $\tau$ be a finite output variable set and let $g\in\mathbb Q[z_t:t\in\tau]$ be homogeneous of degree two and a descendant of $P_{N,q}$. A descendant is obtained by a finite sequence of coordinate derivatives, substitutions of variables by linear forms with nonnegative rational coefficients, and multiplication by nonnegative rational constants. Then $$\operatorname{sig}_+(Q_g)\le1.$$ For a real quadratic form, $\operatorname{sig}_+$ denotes the maximal dimension of a subspace on which it is positive definite. For a rational polynomial $g$, write $H_g$ for the real matrix whose $(i,j)$ entry is the constant coefficient of $\partial_i\partial_j g$, embedded from $\mathbb Q$ into $\mathbb R$, and write $Q_g(v)=v^{\mathsf T}H_gv$.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/RankWeightQuadraticSignature.lean#L361-L504

import Definitions.Def_CountingMatroid_Analysis_CubicTensorContraction
import Definitions.Def_CountingMatroid_Analysis_LorentzianDirectionalSignature
import Definitions.Def_CountingMatroid_Analysis_QuadraticNonpositiveHyperplane
import Definitions.Def_CountingMatroid_Analysis_RankWeightQuadraticSignature
import Definitions.Def_CountingMatroid_Analysis_RankWeightSupportExchange
import Definitions.Def_CountingMatroid_Analysis_SquarefreeCoordinateHessian
import Definitions.Def_CountingMatroid_Model_Prelude
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Multiset.Count
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Instances.Real.Lemmas

namespace CountingMatroid.Analysis.MixedDirectionalRankWeightSignature
end CountingMatroid.Analysis.MixedDirectionalRankWeightSignature
namespace CountingMatroid.Analysis.RankWeightCoordinateLorentzian
end CountingMatroid.Analysis.RankWeightCoordinateLorentzian
namespace CountingMatroid.Analysis.RankWeightCoordinateSignature
end CountingMatroid.Analysis.RankWeightCoordinateSignature
namespace CountingMatroid.Analysis.RankWeightResidualSignature
end CountingMatroid.Analysis.RankWeightResidualSignature
namespace CountingMatroid.Analysis.RankWeightClosurePair
end CountingMatroid.Analysis.RankWeightClosurePair
namespace CountingMatroid.Analysis.ClosureClassQuadraticBound
end CountingMatroid.Analysis.ClosureClassQuadraticBound
namespace CountingMatroid.Analysis.SquarefreeFullDerivative
end CountingMatroid.Analysis.SquarefreeFullDerivative
namespace CountingMatroid.Analysis.BinaryRankWeightSignature
end CountingMatroid.Analysis.BinaryRankWeightSignature
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
namespace CountingMatroid.Analysis.LinearSubstitutionHessian
end CountingMatroid.Analysis.LinearSubstitutionHessian
namespace CountingMatroid.Analysis.LinearPolynomialChainRule
end CountingMatroid.Analysis.LinearPolynomialChainRule
set_option autoImplicit false

/-!
The precise external signature input, separate from the operational rank
correspondence and coefficient extraction proved in the counting paper.
`Descendant` records only partial derivatives, nonnegative linear
substitutions, and nonnegative scalar multiplication. The signature uses
Mathlib's maximum dimension of a positive definite subspace over the reals.
The empty- and singleton-ground signature cases are proved, using the
homogeneous-degree invariant of every descendant. The two-element ground
case is proved by rank submodularity and a two-square calculation, with
the resulting hyperplane transported through every allowed substitution.
The signature case with at most one output variable follows from the ambient
dimension bound. The remaining
Bränden–Huh input is the unresolved borrowed mixed-derivative prerequisite
in `MixedDirectionalRankWeightSignature`. The exact normal
form of a descendant is proved: nonnegative directional derivatives in the
original variables, followed by one nonnegative linear substitution and a
nonnegative scalar. A nonzero quadratic uses exactly ground-set size minus
two derivatives. The unresolved signature bound is applied to this normal
form. A proved nonpositive-hyperplane invariant transports the Hessian
through the final substitution and scaling and recovers the exact orthogonal
kernel used by the signature bound. Only its establishment for the original
mixed directional derivative on ground sets of size at least three remains
open in that support module; no Lorentzian assumption has been introduced.
-/

namespace CountingMatroid.Analysis.RankWeightQuadraticSignature
end CountingMatroid.Analysis.RankWeightQuadraticSignature
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.RankWeightQuadraticSignature

open scoped BigOperators

theorem CountingMatroid.Analysis.RankWeightQuadraticSignature.branden_huh_quadratic_signature {α τ : Type} [Fintype α] [Fintype τ]
    [DecidableEq τ] (N : Matroid α) (hfull : N.E = Set.univ)
    (q : ℚ) (hq : 0 < q) (hqone : q ≤ 1) (g : MvPolynomial τ ℚ)
    (hg : Descendant (tuttePolynomial N q) τ g)
    (hdegree : g.IsHomogeneous 2) :
    sigPos (hessian g).toQuadraticForm' ≤ 1 := by sorry
