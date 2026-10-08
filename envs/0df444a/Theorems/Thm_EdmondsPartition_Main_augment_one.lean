-- Prove2me | Theorems.Thm_EdmondsPartition_Main_augment_one
-- name    : EdmondsPartition.Main.augment_one
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T06:26:24.061746+00:00
-- url     : https://prove2.me/theorems/2c07f1f7-be35-4d9d-a4b8-4dc945bff6fc
-- title:
--   §1.6, proof of THEOREM 1, p. 71 — one-element augmentation: make room for x in a family of k disjoint independent sets
-- statement:
--   Throughout, $M$ is a finite matroid: a finite set of elements (the type $\alpha$, with $M$ the whole set) together with a family of *independent* subsets satisfying **Axiom 1** (every subset of an independent set is independent) and **Axiom 2** (for every subset $A$, all maximal independent subsets of $A$ have the same number of elements). For $A\subseteq M$, the rank $r(A)$ is the largest cardinality of an independent subset of $A$. A span is a set $S$ such that no circuit (minimal dependent set) has exactly one element outside $S$. Assume that every span $S$ satisfies $|S|\le k\cdot r(S)$. Let $I_1,\dots,I_k$ be mutually disjoint independent sets (any of them may be empty) and let $x$ be an element in none of them. Then there are mutually disjoint independent sets $I'_1,\dots,I'_k$ with
--   $$\bigcup_{i=1}^k I'_i=\{x\}\cup\bigcup_{i=1}^k I_i.$$
--
--   This is the heart of the proof of THEOREM 1: elements are rearranged among the $k$ sets so that $x$ fits into one of them while independence and disjointness are preserved, and no previously covered element is lost. Repeating it covers all of $M$.
--
--   **Formalization Note** Lean also assumes that the empty set is independent ($h_0$). The paper's rank, "the number of elements in each maximal independent set contained in $A$", presupposes that every set has an independent subset; with an empty family Axioms 1 and 2 hold vacuously and the statement fails. The conclusion is an equality of unions, so the new family covers exactly the old elements together with $x$.
-- source:
--   Edmonds, Minimum partition of a matroid into independent subsets, J. Res. NBS 69B (1965), p. 71, §1.6, proof of THEOREM 1 ("Let F be a family of k mutually disjoint independent sets of M … to make room for x in one of them")

import Mathlib
import Definitions.Def_WhitneyMatroid_RankIndep_Postulates
import Definitions.Def_EdmondsPartition_Main_Basic

namespace EdmondsPartition.Main

open WhitneyMatroid.RankIndep

theorem augment_one {α : Type*} [Fintype α] [DecidableEq α] (Indep : Finset α → Prop)
    (h1 : IndepI1 Indep) (h2 : Axiom2 Indep) (h0 : Indep ∅) (k : ℕ)
    (hspan : ∀ S : Finset α, IsSpan Indep S → (S.card : ℤ) ≤ (k : ℤ) * rankOfIndep Indep S)
    (I : Fin k → Finset α) (hI : ∀ i, Indep (I i))
    (hdisj : (Set.univ : Set (Fin k)).PairwiseDisjoint I) (x : α) (hx : ∀ i, x ∉ I i) :
    ∃ I' : Fin k → Finset α, (∀ i, Indep (I' i)) ∧ (Set.univ : Set (Fin k)).PairwiseDisjoint I' ∧
      Finset.univ.biUnion I' = insert x (Finset.univ.biUnion I) := by sorry

end EdmondsPartition.Main
