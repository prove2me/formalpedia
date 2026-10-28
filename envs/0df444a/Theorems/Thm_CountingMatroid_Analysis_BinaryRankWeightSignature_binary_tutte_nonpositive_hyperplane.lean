-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_BinaryRankWeightSignature_binary_tutte_nonpositive_hyperplane
-- name    : CountingMatroid.Analysis.BinaryRankWeightSignature.binary_tutte_nonpositive_hyperplane
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T15:27:50.76156+00:00
-- url     : https://prove2.me/theorems/88cfab4d-c371-4f4c-80b4-dbc58b33effb
-- title:
--   Two-element matroid rank weights have a nonpositive Hessian kernel
-- statement:
--   Let $E$ be a two-element finite set, let $N$ be a matroid on $E$, and let $q\in\mathbb Q$ satisfy $0<q\le1$. Write $r_N(A)$ for the finite matroid rank of $A\subseteq E$. In variables $z$ and $(x_a)_{a\in E}$, define $$p(z,x)=\sum_{A\subseteq E}q^{-r_N(A)}z^{2-|A|}\prod_{a\in A}x_a.$$ Let $H$ be its Hessian matrix, viewed over $\mathbb R$; equivalently its entries are the constant coefficients of the second partial derivatives. There exists a real linear functional $\lambda$ on $\mathbb R^{\{z\}\sqcup E}$ such that $$\lambda(v)=0\ \Longrightarrow\ v^{\mathsf T}Hv\le0.$$ This establishes the two-element case of the rank-weight quadratic kernel criterion.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/BinaryRankWeightSignature.lean#L71-L156

import Definitions.Def_CountingMatroid_Analysis_QuadraticNonpositiveHyperplane
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Signature

namespace CountingMatroid.Analysis.BinaryRankWeightSignature
end CountingMatroid.Analysis.BinaryRankWeightSignature
set_option autoImplicit false

/-!
The two-element rank-weight signature calculation. Submodularity bounds the
pair coefficient by the product of the singleton coefficients. The resulting
quadratic has a nonpositive hyperplane, as seen by completing two squares.
-/

namespace CountingMatroid.Analysis.BinaryRankWeightSignature
end CountingMatroid.Analysis.BinaryRankWeightSignature
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.BinaryRankWeightSignature

open QuadraticNonpositiveHyperplane
open scoped BigOperators

theorem CountingMatroid.Analysis.BinaryRankWeightSignature.binary_tutte_nonpositive_hyperplane {α : Type} [Fintype α] [DecidableEq α]
    (N : Matroid α) (q : ℚ) (hq : 0 < q) (hqone : q ≤ 1)
    (htwo : Fintype.card α = 2) :
    let p : MvPolynomial (Option α) ℚ := ∑ A : Finset α,
      MvPolynomial.C ((q ^ (N.eRk (A : Set α)).toNat)⁻¹) *
        MvPolynomial.X none ^ (Fintype.card α - A.card) *
          ∏ a ∈ A, MvPolynomial.X (some a)
    HasNonpositiveHyperplane (Matrix.toQuadraticForm' (fun i j =>
      ((MvPolynomial.constantCoeff (MvPolynomial.pderiv i (MvPolynomial.pderiv j p)) : ℚ) : ℝ))) := by sorry
