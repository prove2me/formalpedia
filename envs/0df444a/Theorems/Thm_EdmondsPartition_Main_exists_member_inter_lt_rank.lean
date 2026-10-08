-- Prove2me | Theorems.Thm_EdmondsPartition_Main_exists_member_inter_lt_rank
-- name    : EdmondsPartition.Main.exists_member_inter_lt_rank
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T06:25:40.562978+00:00
-- url     : https://prove2.me/theorems/09c43ce5-41cc-4134-82f0-184dbc23bb40
-- title:
--   §1.6, proof of THEOREM 1, p. 71 — counting step: some member I of F has |I ∩ S| < r(S)
-- statement:
--   Let $M$ be a finite set with an independence family and rank $r(A)$, the largest cardinality of an independent subset of $A$. Let $I_1,\dots,I_k$ be mutually disjoint subsets of $M$ and let $x$ be an element in none of them. If $S\subseteq M$ contains $x$ and $|S|\le k\cdot r(S)$, then there is an index $i$ with
--   $$|I_i\cap S|<r(S).$$
--
--   In the main proof this is applied to the nested spans $S_0=M\supseteq S_1\supseteq\cdots$: if every $I_i$ had $r(S)$ elements in $S$, their disjoint union together with $x$ would give more than $k\cdot r(S)$ elements in $S$.
--
--   **Formalization Note** The argument is pure counting, so no matroid axiom and no independence of the $I_i$ is assumed; this makes the statement stronger than the page's setting, where the $I_i$ are the independent members of the family $F$.
-- source:
--   Edmonds, Minimum partition of a matroid into independent subsets, J. Res. NBS 69B (1965), p. 71, §1.6, proof of THEOREM 1 ("Similarly, x ∈ S₁ = S(I₁) implies …")

import Mathlib
import Definitions.Def_WhitneyMatroid_RankIndep_Postulates
import Definitions.Def_EdmondsPartition_Main_Basic

namespace EdmondsPartition.Main

open WhitneyMatroid.RankIndep

theorem exists_member_inter_lt_rank {α : Type*} [Fintype α] [DecidableEq α]
    (Indep : Finset α → Prop) (k : ℕ) (I : Fin k → Finset α)
    (hdisj : (Set.univ : Set (Fin k)).PairwiseDisjoint I) (x : α) (hx : ∀ i, x ∉ I i)
    (S : Finset α) (hxS : x ∈ S) (hS : (S.card : ℤ) ≤ (k : ℤ) * rankOfIndep Indep S) :
    ∃ i : Fin k, ((I i ∩ S).card : ℤ) < rankOfIndep Indep S := by sorry

end EdmondsPartition.Main
