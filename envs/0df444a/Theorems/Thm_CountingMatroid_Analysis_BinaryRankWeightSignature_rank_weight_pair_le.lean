-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_BinaryRankWeightSignature_rank_weight_pair_le
-- name    : CountingMatroid.Analysis.BinaryRankWeightSignature.rank_weight_pair_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T14:44:56.642011+00:00
-- url     : https://prove2.me/theorems/ea51ef83-3369-468c-87ca-48fa665d389e
-- title:
--   Two-element inverse rank weights are bounded by the singleton product
-- statement:
--   Let $N$ be a matroid on a finite type $\alpha$, let $0<q\le1$ be rational, and let $r_N(A)$ denote its finite rank on $A\subseteq\alpha$. For all $s,t\in\alpha$, $$q^{-r_N(\{s,t\})}\le q^{-r_N(\{s\})}q^{-r_N(\{t\})}.$$
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/BinaryRankWeightSignature.lean#L51-L69

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

theorem CountingMatroid.Analysis.BinaryRankWeightSignature.rank_weight_pair_le {α : Type} [Finite α] (N : Matroid α)
    (q : ℚ) (hq : 0 < q) (hqone : q ≤ 1) (s t : α) :
    (q ^ (N.eRk ({s, t} : Set α)).toNat)⁻¹ ≤
      (q ^ (N.eRk ({s} : Set α)).toNat)⁻¹ *
        (q ^ (N.eRk ({t} : Set α)).toNat)⁻¹ := by sorry
