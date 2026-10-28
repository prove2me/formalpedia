-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_SquarefreeCoordinateHessian_squarefree_coordinate_hessian
-- name    : CountingMatroid.Analysis.SquarefreeCoordinateHessian.squarefree_coordinate_hessian
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T15:53:07.235744+00:00
-- url     : https://prove2.me/theorems/cde695cd-f075-45c2-9b38-c90de3937a84
-- title:
--   A quadratic coordinate derivative has a scaled residual Hessian
-- statement:
--   Let $\alpha$ be a finite set of size $m$, let $w:\mathcal P(\alpha)\to\mathbb Q$ be arbitrary, and use a distinguished homogenizing variable $z$ together with label variables $x_a$ for $a\in\alpha$. Define $$p_w(z,x)=\sum_{A\subseteq\alpha}w(A)z^{m-|A|}\prod_{a\in A}x_a.$$ For a finite list $L$ of coordinates from $\{z\}\sqcup\alpha$, write $D_L$ for the composition of the corresponding partial derivatives, and let $L_\alpha$ be the list obtained by deleting the occurrences of $z$. Suppose $|L|+2=m$. For $S\subseteq\alpha$ and $k\in\mathbb N$, define the real symmetric matrix $H(w,S,k)$ on $\{z\}\sqcup\alpha$ by $$H_{zz}=(k+2)(k+1)w(S),\qquad H_{za}=H_{az}=\begin{cases}0&a\in S,\\(k+1)w(S\cup\{a\})&a\notin S,\end{cases}$$ and $$H_{ab}=\begin{cases}0&a\in S\text{ or }b\in S\text{ or }a=b,\\w(S\cup\{a,b\})&\text{otherwise}.\end{cases}$$ Rational coefficients are viewed in $\mathbb R$. For a polynomial $f$, let $Q_f(v)=\sum_{i,j}[1](\partial_i\partial_j f)v_iv_j$, where $[1]$ denotes constant coefficient and $v\in\mathbb R^{\{z\}\sqcup\alpha}$. Then there exist $S\subseteq\alpha$, $k\in\mathbb N$, and $c\in\mathbb R$ such that $$c\ge0,\qquad |S|+k+2=m,\qquad Q_{D_Lp_w}(v)=c\,v^{\mathsf T}H(w,S,k)v\quad\text{for every }v.$$
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/SquarefreeCoordinateHessian.lean#L109-L223

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

theorem CountingMatroid.Analysis.SquarefreeCoordinateHessian.squarefree_coordinate_hessian {α : Type} [Fintype α] [DecidableEq α]
    (w : Finset α → ℚ) (xs : List (Option α))
    (hlength : xs.length + 2 = Fintype.card α) :
    ∃ (S : Finset α) (k : ℕ) (c : ℝ),
      0 ≤ c ∧ S.card + k + 2 = Fintype.card α ∧
      constantHessianForm
        (xs.foldr (fun s f => MvPolynomial.pderiv s f)
          (∑ A : Finset α,
            MvPolynomial.C (w A) *
              MvPolynomial.X none ^ (Fintype.card α - A.card) *
                ∏ a ∈ A, MvPolynomial.X (some a))) =
        c • (squarefreeResidualHessian w S k).toQuadraticForm' := by sorry
