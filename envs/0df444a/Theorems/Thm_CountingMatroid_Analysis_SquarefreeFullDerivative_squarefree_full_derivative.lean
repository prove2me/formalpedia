-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_SquarefreeFullDerivative_squarefree_full_derivative
-- name    : CountingMatroid.Analysis.SquarefreeFullDerivative.squarefree_full_derivative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T15:27:10.208828+00:00
-- url     : https://prove2.me/theorems/4553c5eb-f99b-4c8e-a3b8-ec9d29abc9be
-- title:
--   A full squarefree derivative extracts its subset weight times a factorial
-- statement:
--   Let $\alpha$ be a finite set of size $m$, let $w:\mathcal P(\alpha)\to\mathbb Q$ be arbitrary, and use a distinguished homogenizing variable $z$ together with label variables $x_a$ for $a\in\alpha$. Define $$p_w(z,x)=\sum_{A\subseteq\alpha}w(A)z^{m-|A|}\prod_{a\in A}x_a.$$ For a finite list $L$ of coordinates from $\{z\}\sqcup\alpha$, write $D_L$ for the composition of the corresponding partial derivatives, and let $L_\alpha$ be the list obtained by deleting the occurrences of $z$. Assume $L_\alpha$ has no repetitions and $|L|=m$. Let $S\subseteq\alpha$ be the set of labels in $L_\alpha$ and let $k$ count the occurrences of $z$ in $L$. Then $$[1](D_Lp_w)=w(S)\,k!,$$ where $[1]$ denotes constant coefficient.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/SquarefreeFullDerivative.lean#L87-L113

import Definitions.Def_CountingMatroid_Analysis_CubicTensorContraction
import Definitions.Def_CountingMatroid_Analysis_LorentzianDirectionalSignature
import Definitions.Def_CountingMatroid_Analysis_QuadraticNonpositiveHyperplane
import Definitions.Def_CountingMatroid_Analysis_RankWeightSupportExchange
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

/-! Coefficient extraction for full coordinate derivatives of squarefree-label
homogenizations. The coefficient multiplier counts repeated homogenizer
coordinates while the label coordinates are distinct. -/

namespace CountingMatroid.Analysis.SquarefreeFullDerivative
end CountingMatroid.Analysis.SquarefreeFullDerivative
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.SquarefreeFullDerivative

open scoped BigOperators
open RankWeightSupportExchange

theorem CountingMatroid.Analysis.SquarefreeFullDerivative.squarefree_full_derivative {α : Type} [Fintype α] [DecidableEq α]
    (w : Finset α → ℚ) (xs : List (Option α))
    (hnd : (xs.filterMap id).Nodup) (hlen : xs.length = Fintype.card α) :
    MvPolynomial.constantCoeff
      (xs.foldr (fun s f => MvPolynomial.pderiv s f)
        (∑ A : Finset α, MvPolynomial.C (w A) *
          MvPolynomial.X none ^ (Fintype.card α - A.card) *
            ∏ a ∈ A, MvPolynomial.X (some a))) =
      w (xs.filterMap id).toFinset * (Nat.factorial (xs.count none) : ℚ) := by sorry
