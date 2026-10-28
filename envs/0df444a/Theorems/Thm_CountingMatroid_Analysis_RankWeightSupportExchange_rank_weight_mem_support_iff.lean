-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_RankWeightSupportExchange_rank_weight_mem_support_iff
-- name    : CountingMatroid.Analysis.RankWeightSupportExchange.rank_weight_mem_support_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T14:45:58.386437+00:00
-- url     : https://prove2.me/theorems/46be7d65-8d06-4285-9c8b-8872977cf260
-- title:
--   Exact support of the homogenized rank-weight polynomial
-- statement:
--   Let $E$ be a finite set of size $d$, $N$ a matroid on $E$, and $r_N(A)$ the finite natural-number rank of $A\subseteq E$. Introduce a fresh homogenizing variable $z_0$, distinct from the variables $z_a$ for $a\in E$, and define $$P_{N,q}(z_0,z)=\sum_{A\subseteq E}(q^{r_N(A)})^{-1}z_0^{d-|A|}\prod_{a\in A}z_a.$$ Let $q>0$ be rational. For $A\subseteq E$, let $e_A$ be the exponent vector with homogenizer coordinate $d-|A|$ and label coordinates $\mathbf1_{\{a\in A\}}$. For every exponent vector $m$ on $\{0\}\sqcup E$, $$m\in\operatorname{supp}(P_{N,q})\quad\Longleftrightarrow\quad\exists A\subseteq E,\ m=e_A.$$ Here support consists of monomials with nonzero coefficient.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/RankWeightSupportExchange.lean#L56-L79

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

/-! The subset exponent description of the rank-weight polynomial support.
The exchange condition depends only on the subsets, not on matroid ranks. -/

namespace CountingMatroid.Analysis.RankWeightSupportExchange
end CountingMatroid.Analysis.RankWeightSupportExchange
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.RankWeightSupportExchange

open scoped BigOperators
open LorentzianDirectionalSignature

theorem CountingMatroid.Analysis.RankWeightSupportExchange.rank_weight_mem_support_iff {α : Type} [Fintype α] [DecidableEq α]
    (N : Matroid α) (q : ℚ) (hq : 0 < q) (m : Option α →₀ ℕ) :
    m ∈ (∑ A : Finset α,
      MvPolynomial.C ((q ^ (N.eRk (A : Set α)).toNat)⁻¹) *
        MvPolynomial.X none ^ (Fintype.card α - A.card) *
          ∏ a ∈ A, MvPolynomial.X (some a)).support ↔
      ∃ A : Finset α, m = subsetExponent A := by sorry
