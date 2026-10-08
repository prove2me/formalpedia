-- Prove2me | Theorems.Thm_EdmondsPartition_Main_partition_of_counting
-- name    : EdmondsPartition.Main.partition_of_counting
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-06T15:23:37.871272+00:00
-- url     : https://prove2.me/theorems/67b1d4a5-05e6-4da8-a6b3-822eaf87d3db
-- title:
--   Edmonds' partition theorem in counting form
-- statement:
--   Throughout, $M$ is a finite matroid: a finite set of elements (the type $\alpha$) together with a family of *independent* subsets satisfying **Axiom 1** (every subset of an independent set is independent) and **Axiom 2** (for every subset $A$, all maximal independent subsets of $A$ have the same number of elements). The rank $r(A)$ is the largest cardinality of an independent subset of $A$.
--
--   Let $k\in\mathbb N$ and let $U\subseteq M$ satisfy
--   $$|J|\le k\cdot r(J)\qquad\text{for every } J\subseteq U .$$
--   Then there are mutually disjoint independent sets $I_1,\dots,I_k$ (some possibly empty) with $I_1\cup\dots\cup I_k=U$.
--
--   This is the "if" part of Edmonds' THEOREM 1, stated for an arbitrary subset $U$ of the matroid. The proof applies Rado's theorem (`rado_rank`) to the $k$-fold direct sum of the matroid on $M\times\{1,\dots,k\}$ with the family $A_e=\{e\}\times\{1,\dots,k\}$, $e\in U$: Rado's condition for a set $J$ of elements is exactly $|J|\le k\,r(J)$, and an independent transversal is the same as a placement of every element of $U$ into one of the $k$ classes so that each class is independent.
--
--   **Formalization Note** Lean also assumes that the empty set is independent ($h_0$), as in the milestone statements of this mission; the paper's rank presupposes that every set has an independent subset.
-- source:
--   J. Edmonds, Minimum partition of a matroid into independent subsets, J. Res. NBS 69B (1965), p. 69, THEOREM 1 (counting form; proved here by Rado's theorem on the k-fold direct sum instead of Edmonds' augmenting construction)

import Mathlib
import Definitions.Def_WhitneyMatroid_RankIndep_Postulates
import Definitions.Def_EdmondsPartition_Main_Basic

namespace EdmondsPartition.Main

open WhitneyMatroid.RankIndep

theorem partition_of_counting {α : Type*} [Fintype α] [DecidableEq α] (Indep : Finset α → Prop)
    (h1 : IndepI1 Indep) (h2 : Axiom2 Indep) (h0 : Indep ∅) (k : ℕ) (U : Finset α)
    (hU : ∀ J : Finset α, J ⊆ U → (J.card : ℤ) ≤ (k : ℤ) * rankOfIndep Indep J) :
    ∃ I : Fin k → Finset α, (∀ i, Indep (I i)) ∧
      (Set.univ : Set (Fin k)).PairwiseDisjoint I ∧ Finset.univ.biUnion I = U := by sorry

end EdmondsPartition.Main
