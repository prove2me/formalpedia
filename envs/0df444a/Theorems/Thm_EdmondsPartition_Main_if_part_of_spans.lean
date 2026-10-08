-- Prove2me | Theorems.Thm_EdmondsPartition_Main_if_part_of_spans
-- name    : EdmondsPartition.Main.if_part_of_spans
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T06:26:05.205987+00:00
-- url     : https://prove2.me/theorems/f651df72-0a5c-4277-b1e7-0401acc8dbfd
-- title:
--   §1.6, proof of THEOREM 1, p. 70 — the "if" part needs |S| ≤ k·r(S) only for spans S
-- statement:
--   Throughout, $M$ is a finite matroid: a finite set of elements (the type $\alpha$, with $M$ the whole set) together with a family of *independent* subsets satisfying **Axiom 1** (every subset of an independent set is independent) and **Axiom 2** (for every subset $A$, all maximal independent subsets of $A$ have the same number of elements). For $A\subseteq M$, the rank $r(A)$ is the largest cardinality of an independent subset of $A$. A span is a set $S$ such that no circuit (minimal dependent set) has exactly one element outside $S$. If every span $S$ of $M$ satisfies
--   $$|S|\le k\cdot r(S),$$
--   then $M$ can be partitioned into $k$ mutually disjoint independent sets (some possibly empty).
--
--   Since every span is a subset of $M$, this strengthens the "if" direction of THEOREM 1: the inequality need only be checked on spans.
--
--   **Formalization Note** Lean also assumes that the empty set is independent ($h_0$). The paper's rank, "the number of elements in each maximal independent set contained in $A$", presupposes that every set has an independent subset; with an empty family Axioms 1 and 2 hold vacuously and the statement fails. The partition is an indexed family of $k$ pairwise disjoint independent sets covering $M$, with empty parts allowed.
-- source:
--   Edmonds, Minimum partition of a matroid into independent subsets, J. Res. NBS 69B (1965), p. 70, §1.6, proof of THEOREM 1 (the "if" part): "Actually, it is sufficient that for every span S in M, |S| ≤ k·r(S)"; the argument ends on p. 71

import Mathlib
import Definitions.Def_WhitneyMatroid_RankIndep_Postulates
import Definitions.Def_EdmondsPartition_Main_Basic

namespace EdmondsPartition.Main

open WhitneyMatroid.RankIndep

theorem if_part_of_spans {α : Type*} [Fintype α] [DecidableEq α] (Indep : Finset α → Prop)
    (h1 : IndepI1 Indep) (h2 : Axiom2 Indep) (h0 : Indep ∅) (k : ℕ)
    (hspan : ∀ S : Finset α, IsSpan Indep S → (S.card : ℤ) ≤ (k : ℤ) * rankOfIndep Indep S) :
    ∃ I : Fin k → Finset α, IsPartitionInto Indep k I := by sorry

end EdmondsPartition.Main
