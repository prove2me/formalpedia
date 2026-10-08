-- Prove2me | Theorems.Thm_EdmondsPartition_Main_theorem_1
-- name    : EdmondsPartition.Main.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T06:26:34.395105+00:00
-- url     : https://prove2.me/theorems/22340024-5c57-4560-9d70-0f50ae435648
-- title:
--   THEOREM 1, p. 69 — a matroid M splits into k independent sets iff no subset A has |A| > k·r(A)
-- statement:
--   Throughout, $M$ is a finite matroid: a finite set of elements (the type $\alpha$, with $M$ the whole set) together with a family of *independent* subsets satisfying **Axiom 1** (every subset of an independent set is independent) and **Axiom 2** (for every subset $A$, all maximal independent subsets of $A$ have the same number of elements). For $A\subseteq M$, the rank $r(A)$ is the largest cardinality of an independent subset of $A$. Let $k\ge 0$ be an integer. Then the elements of $M$ can be partitioned into as few as $k$ sets, each of which is independent, if and only if there is no subset $A$ of $M$ with
--   $$|A|>k\cdot r(A).$$
--
--   This is Edmonds's matroid partition theorem. It gives a good characterization of the minimum number of independent sets needed to cover a matroid: a partition certifies that $k$ sets suffice, and a single set $A$ with $|A|>k\,r(A)$ certifies that they do not. For graphic matroids it specializes to Nash-Williams's theorem on covering a graph by forests, and it is the starting point of matroid union and matroid intersection theory.
--
--   **Formalization Note** Lean also assumes that the empty set is independent ($h_0$). The paper's rank, "the number of elements in each maximal independent set contained in $A$", presupposes that every set has an independent subset; with an empty family Axioms 1 and 2 hold vacuously and the statement fails. A partition into $k$ sets is an indexed family of $k$ pairwise disjoint independent sets whose union is $M$; any number of them may be empty, as on p. 71. The rank is integer-valued and the inequality is compared in $\mathbb Z$. The case $k=0$ is included (it says $M$ is empty iff no $A$ has $|A|>0$).
-- source:
--   Edmonds, Minimum partition of a matroid into independent subsets, J. Res. NBS 69B (1965), p. 69, THEOREM 1

import Mathlib
import Definitions.Def_WhitneyMatroid_RankIndep_Postulates
import Definitions.Def_EdmondsPartition_Main_Basic

namespace EdmondsPartition.Main

open WhitneyMatroid.RankIndep

theorem theorem_1 {α : Type*} [Fintype α] [DecidableEq α] (Indep : Finset α → Prop)
    (h1 : IndepI1 Indep) (h2 : Axiom2 Indep) (h0 : Indep ∅) (k : ℕ) :
    (∃ I : Fin k → Finset α, IsPartitionInto Indep k I) ↔
      ¬ ∃ A : Finset α, (k : ℤ) * rankOfIndep Indep A < (A.card : ℤ) := by sorry

end EdmondsPartition.Main
