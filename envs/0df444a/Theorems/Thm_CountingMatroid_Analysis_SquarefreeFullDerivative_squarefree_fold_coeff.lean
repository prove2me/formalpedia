-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_SquarefreeFullDerivative_squarefree_fold_coeff
-- name    : CountingMatroid.Analysis.SquarefreeFullDerivative.squarefree_fold_coeff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T14:45:01.738968+00:00
-- url     : https://prove2.me/theorems/91001136-b155-45ec-9480-48d398f73040
-- title:
--   Coefficient extraction after squarefree label differentiation
-- statement:
--   Let $\alpha$ be a set with decidable equality, and use coordinates $\{z\}\sqcup\alpha$. Let $p$ be a polynomial in these coordinates over $\mathbb Q$, let $L$ be a finite coordinate list, and let $m$ be a finitely supported nonnegative integer exponent vector. Write $D_L$ for the listed partial derivatives, $S$ for the set of label coordinates appearing in $L$, and $k$ for the number of occurrences of $z$. Assume no label occurs twice in $L$ and $m(a)=0$ for every $a\in S$. If $\mathbf e_i$ denotes the unit exponent at coordinate $i$ and $[x^v]p$ denotes the coefficient at exponent $v$, then $$[x^m](D_Lp)=\left[x^{\,m+k\mathbf e_z+\sum_{a\in S}\mathbf e_a}\right]p\;\prod_{j=1}^{k}(m(z)+j).$$ The empty product is $1$.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/SquarefreeFullDerivative.lean#L14-L72

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

theorem CountingMatroid.Analysis.SquarefreeFullDerivative.squarefree_fold_coeff {α : Type} [DecidableEq α]
    (xs : List (Option α)) (p : MvPolynomial (Option α) ℚ)
    (m : Option α →₀ ℕ) (hnd : (xs.filterMap id).Nodup)
    (hm : ∀ a ∈ xs.filterMap id, m (some a) = 0) :
    (xs.foldr (fun s f => MvPolynomial.pderiv s f) p).coeff m =
      p.coeff (m + (Finsupp.single none (xs.count none) +
        ∑ a ∈ (xs.filterMap id).toFinset, Finsupp.single (some a) 1)) *
        ((m none + 1).ascFactorial (xs.count none) : ℚ) := by sorry
