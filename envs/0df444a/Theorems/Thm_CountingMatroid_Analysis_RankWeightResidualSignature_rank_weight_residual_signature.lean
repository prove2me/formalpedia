-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_RankWeightResidualSignature_rank_weight_residual_signature
-- name    : CountingMatroid.Analysis.RankWeightResidualSignature.rank_weight_residual_signature
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T15:29:19.597866+00:00
-- url     : https://prove2.me/theorems/2c911d7d-b7f2-49bb-a3b8-c829e7284875
-- title:
--   An explicit nonpositive hyperplane for the residual rank-weight Hessian
-- statement:
--   Let $E$ be a finite set of size $d$, let $N$ be a matroid with full ground $E$, and let rational $0<q\le1$. Put $w(A)=(q^{r_N(A)})^{-1}$, viewed in $\mathbb R$. Let $S\subseteq E$ and $k\in\mathbb N$ satisfy $|S|+k+2=d$. On coordinates $\{0\}\sqcup E$, define a symmetric matrix $H$ by $$H_{00}=(k+2)(k+1)w(S),\qquad H_{0a}=H_{a0}=\begin{cases}(k+1)w(S\cup\{a\}),&a\notin S,\\0,&a\in S,\end{cases}$$ and $$H_{ab}=\begin{cases}w(S\cup\{a,b\}),&a,b\notin S,\ a\ne b,\\0,&\text{otherwise}.\end{cases}$$ Then $$\exists\ell:\mathbb R^{\{0\}\sqcup E}\to\mathbb R\text{ linear},\qquad \ell(v)=0\Longrightarrow v^{\mathsf T}Hv\le0.$$
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/RankWeightResidualSignature.lean#L20-L149

import Definitions.Def_CountingMatroid_Analysis_CubicTensorContraction
import Definitions.Def_CountingMatroid_Analysis_LorentzianDirectionalSignature
import Definitions.Def_CountingMatroid_Analysis_QuadraticNonpositiveHyperplane
import Definitions.Def_CountingMatroid_Analysis_RankWeightSupportExchange
import Definitions.Def_CountingMatroid_Analysis_SquarefreeCoordinateHessian
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
set_option autoImplicit false

/-! The matroid part of the coordinate-signature calculation, separated from
the polynomial differentiation identity. The residual matrix uses ranks of
the selected set and its one- and two-element extensions. Its nonpositive
hyperplane is explicit. Rank increments identify parallel closure classes,
and label and class Cauchy–Schwarz estimates prove the matrix nonpositive
on that hyperplane. -/

namespace CountingMatroid.Analysis.RankWeightResidualSignature
end CountingMatroid.Analysis.RankWeightResidualSignature
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.RankWeightResidualSignature

open scoped BigOperators
open QuadraticNonpositiveHyperplane SquarefreeCoordinateHessian

theorem CountingMatroid.Analysis.RankWeightResidualSignature.rank_weight_residual_signature {α : Type} [Fintype α] [DecidableEq α]
    (N : Matroid α) (hfull : N.E = Set.univ)
    (q : ℚ) (hq : 0 < q) (hqone : q ≤ 1)
    (S : Finset α) (k : ℕ) (hsize : S.card + k + 2 = Fintype.card α) :
    HasNonpositiveHyperplane
      (squarefreeResidualHessian
        (fun A : Finset α => (q ^ (N.eRk (A : Set α)).toNat)⁻¹)
        S k).toQuadraticForm' := by sorry
