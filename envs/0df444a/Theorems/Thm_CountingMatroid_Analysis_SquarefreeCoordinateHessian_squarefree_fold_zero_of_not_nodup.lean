-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_SquarefreeCoordinateHessian_squarefree_fold_zero_of_not_nodup
-- name    : CountingMatroid.Analysis.SquarefreeCoordinateHessian.squarefree_fold_zero_of_not_nodup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T15:27:11.253104+00:00
-- url     : https://prove2.me/theorems/243d54a2-ccc2-46be-a610-97a66d3b6c31
-- title:
--   Repeating a label derivative annihilates a squarefree homogenization
-- statement:
--   Let $\alpha$ be a finite set of size $m$, let $w:\mathcal P(\alpha)\to\mathbb Q$ be arbitrary, and use a distinguished homogenizing variable $z$ together with label variables $x_a$ for $a\in\alpha$. Define $$p_w(z,x)=\sum_{A\subseteq\alpha}w(A)z^{m-|A|}\prod_{a\in A}x_a.$$ For a finite list $L$ of coordinates from $\{z\}\sqcup\alpha$, write $D_L$ for the composition of the corresponding partial derivatives, and let $L_\alpha$ be the list obtained by deleting the occurrences of $z$. If $L_\alpha$ contains a repeated label, then $$D_Lp_w=0.$$
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/SquarefreeCoordinateHessian.lean#L77-L107

import Definitions.Def_CountingMatroid_Analysis_CubicTensorContraction
import Definitions.Def_CountingMatroid_Analysis_LorentzianDirectionalSignature
import Definitions.Def_CountingMatroid_Analysis_QuadraticNonpositiveHyperplane
import Definitions.Def_CountingMatroid_Analysis_RankWeightSupportExchange
import Definitions.Def_CountingMatroid_Analysis_SquarefreeCoordinateHessian
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Fintype.Powerset
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
set_option autoImplicit false

/-! Coordinate differentiation of a homogeneous polynomial whose label
variables are squarefree reduces its constant Hessian to a residual matrix.
The matrix records the selected labels and the number of homogenizer
derivatives. This calculation concerns arbitrary subset coefficients and
does not assume a matroid signature bound. -/

namespace CountingMatroid.Analysis.SquarefreeCoordinateHessian
end CountingMatroid.Analysis.SquarefreeCoordinateHessian
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.SquarefreeCoordinateHessian

open scoped BigOperators
open LorentzianDirectionalSignature

theorem CountingMatroid.Analysis.SquarefreeCoordinateHessian.squarefree_fold_zero_of_not_nodup {α : Type} [Fintype α] [DecidableEq α]
    (w : Finset α → ℚ) (xs : List (Option α)) (hnd : ¬ (xs.filterMap id).Nodup) :
    xs.foldr (fun s f => MvPolynomial.pderiv s f)
      (∑ A : Finset α, MvPolynomial.C (w A) *
        MvPolynomial.X none ^ (Fintype.card α - A.card) *
          ∏ a ∈ A, MvPolynomial.X (some a)) = 0 := by sorry
