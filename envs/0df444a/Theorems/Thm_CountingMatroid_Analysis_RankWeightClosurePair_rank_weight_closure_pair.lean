-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_RankWeightClosurePair_rank_weight_closure_pair
-- name    : CountingMatroid.Analysis.RankWeightClosurePair.rank_weight_closure_pair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T14:44:55.90566+00:00
-- url     : https://prove2.me/theorems/580b6a18-39db-4bf7-879e-063c6ca8638a
-- title:
--   Exact pair factor for inverse rank weights
-- statement:
--   Let $E$ be finite, let $N$ be a matroid with ground set all of $E$, let $X\subseteq E$, and let $q>0$ be rational. Write $w(A)=(q^{r_N(A)})^{-1}$, where $r_N(A)$ is the finite rank, and let $\operatorname{cl}$ denote matroid closure. For any $a,b\in E$, including $a=b$, $$w(X\cup\{a,b\})w(X)=\gamma\,w(X\cup\{a\})w(X\cup\{b\}),$$ where $$\gamma=\begin{cases}q,&a,b\notin\operatorname{cl}(X)\text{ and }\operatorname{cl}(X\cup\{a\})=\operatorname{cl}(X\cup\{b\}),\\1,&\text{otherwise}.\end{cases}$$
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/RankWeightClosurePair.lean#L27-L76

import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Tactic

namespace CountingMatroid.Analysis.RankWeightClosurePair
end CountingMatroid.Analysis.RankWeightClosurePair
set_option autoImplicit false

/-! Rank increments identify the exact normalized coefficient of a pair of
labels: a pair of nonloops in the same closure class receives the factor q,
and every other pair receives the factor one. -/

namespace CountingMatroid.Analysis.RankWeightClosurePair
end CountingMatroid.Analysis.RankWeightClosurePair
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.RankWeightClosurePair
open scoped Classical

theorem CountingMatroid.Analysis.RankWeightClosurePair.rank_weight_closure_pair {α : Type} [Finite α]
    (N : Matroid α) (hfull : N.E = Set.univ) (X : Set α)
    (q : ℚ) (hq : 0 < q) (a b : α) :
    (q ^ (N.eRk (insert a (insert b X))).toNat)⁻¹ *
      (q ^ (N.eRk X).toNat)⁻¹ =
      (if a ∉ N.closure X ∧ b ∉ N.closure X ∧
          N.closure (insert a X) = N.closure (insert b X) then q else 1) *
        (q ^ (N.eRk (insert a X)).toNat)⁻¹ *
        (q ^ (N.eRk (insert b X)).toNat)⁻¹ := by sorry
