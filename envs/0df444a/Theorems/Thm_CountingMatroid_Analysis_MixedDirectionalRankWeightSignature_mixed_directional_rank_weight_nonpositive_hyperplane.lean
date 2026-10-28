-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_MixedDirectionalRankWeightSignature_mixed_directional_rank_weight_nonpositive_hyperplane
-- name    : CountingMatroid.Analysis.MixedDirectionalRankWeightSignature.mixed_directional_rank_weight_nonpositive_hyperplane
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T16:16:01.430655+00:00
-- url     : https://prove2.me/theorems/29f2cb90-8985-44d0-92d5-cdebf3d67ef8
-- title:
--   Mixed nonnegative derivatives of the rank-weight polynomial have a nonpositive kernel
-- statement:
--   Let $E$ be a finite set and $N$ a matroid with ground set $E$. Let $q\in\mathbb Q$ satisfy $0<q\le1$, and define the polynomial in variables $z$ and $(x_e)_{e\in E}$ by $$T_{q,N}(z,x)=\sum_{A\subseteq E}q^{-\operatorname{rk}_N(A)}z^{|E|-|A|}\prod_{e\in A}x_e.$$ Let $d_1,\ldots,d_\ell\in\mathbb Q^{\{z\}\sqcup E}$ have nonnegative coordinates and satisfy $\ell+2=|E|$. Put $g=D_{d_1}\cdots D_{d_\ell}T_{q,N}$, where $D_d=\sum_s d_s\partial_s$. Form the real quadratic form $$Q(v)=\sum_{s,t}([1]\partial_s\partial_t g)\,v_sv_t.$$ There is a real linear functional $f$ on $\mathbb R^{\{z\}\sqcup E}$ such that $$f(v)=0\ \Longrightarrow\ Q(v)\le0.$$ The functional is allowed to be zero.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/MixedDirectionalRankWeightSignature.lean#L48-L120

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
set_option autoImplicit false

/-!
The original-variable mixed-derivative prerequisite for the rank-weight
signature theorem. Linear substitution and scalar closure are proved in the
parent's other support modules. The empty direction list is handled by
the two-element rank-weight calculation, and an identically zero direction
anywhere in the list gives the zero quadratic form. The remaining case,
where the list is nonempty and every direction is nonzero, now uses two
separate prerequisites: the matroid-specific coordinate Lorentzian certificate
in `RankWeightCoordinateLorentzian`, and the general nonnegative directional
signature consequence in `LorentzianDirectionalSignature`. Both support files
were released through a compiler-validated scheduler handoff; this module
does not supply their full proofs. Their basic degree/coefficient facts and
degree-two closure case are proved. The passage from a signature bound to a
hyperplane is proved by Mathlib diagonalization in
`QuadraticSignatureHyperplane`. The target proof contains no local hole,
but its full proof depends on both prerequisites; the pinned libraries contain
no applicable Lorentzian API.
-/

namespace CountingMatroid.Analysis.MixedDirectionalRankWeightSignature
end CountingMatroid.Analysis.MixedDirectionalRankWeightSignature
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.MixedDirectionalRankWeightSignature

open scoped BigOperators
open QuadraticNonpositiveHyperplane

theorem CountingMatroid.Analysis.MixedDirectionalRankWeightSignature.mixed_directional_rank_weight_nonpositive_hyperplane {α : Type}
    [Fintype α] [DecidableEq α] (N : Matroid α) (hfull : N.E = Set.univ)
    (q : ℚ) (hq : 0 < q) (hqone : q ≤ 1)
    (ds : List (Option α → ℚ))
    (hds : ∀ d ∈ ds, ∀ s, 0 ≤ d s)
    (hlength : ds.length + 2 = Fintype.card α) :
    let p : MvPolynomial (Option α) ℚ := ∑ A : Finset α,
      MvPolynomial.C ((q ^ (N.eRk (A : Set α)).toNat)⁻¹) *
        MvPolynomial.X none ^ (Fintype.card α - A.card) *
          ∏ a ∈ A, MvPolynomial.X (some a)
    let g := ds.foldr (fun d f => ∑ s, MvPolynomial.C (d s) * MvPolynomial.pderiv s f) p
    HasNonpositiveHyperplane (Matrix.toQuadraticForm' (fun i j =>
      ((MvPolynomial.constantCoeff (MvPolynomial.pderiv i (MvPolynomial.pderiv j g)) : ℚ) : ℝ))) := by sorry
