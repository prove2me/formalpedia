-- Prove2me | Theorems.Thm_EdmondsPartition_Main_proposition_4
-- name    : EdmondsPartition.Main.proposition_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T06:23:19.775972+00:00
-- url     : https://prove2.me/theorems/13532ec2-567d-4c13-8858-2f7cff511db5
-- title:
--   PROPOSITION 4, p. 70 — e ∈ S(A) iff e ∈ A or some circuit C has C − A = {e}
-- statement:
--   Throughout, $M$ is a finite matroid: a finite set of elements (the type $\alpha$, with $M$ the whole set) together with a family of *independent* subsets satisfying **Axiom 1** (every subset of an independent set is independent) and **Axiom 2** (for every subset $A$, all maximal independent subsets of $A$ have the same number of elements). For $A\subseteq M$, the rank $r(A)$ is the largest cardinality of an independent subset of $A$. A circuit is a minimal dependent set, and a span is a set $S$ such that no circuit has exactly one element outside $S$; the span $S(A)$ of $A$ is the minimal span containing $A$. Then for every $A\subseteq M$ and every element $e$,
--   $$e\in S(A)\iff e\in A\ \text{ or there is a circuit } C \text{ with } C\setminus A=\{e\}.$$
--
--   This gives the span an explicit description in terms of circuits and is the form in which spans are used in the main proof.
--
--   **Formalization Note** Lean also assumes that the empty set is independent ($h_0$). The paper's rank, "the number of elements in each maximal independent set contained in $A$", presupposes that every set has an independent subset; with an empty family Axioms 1 and 2 hold vacuously and the statement fails. $S(A)$ is the intersection of all spans containing $A$.
-- source:
--   Edmonds, Minimum partition of a matroid into independent subsets, J. Res. NBS 69B (1965), p. 70, PROPOSITION 4

import Mathlib
import Definitions.Def_WhitneyMatroid_RankIndep_Postulates
import Definitions.Def_EdmondsPartition_Main_Basic

namespace EdmondsPartition.Main

open WhitneyMatroid.RankIndep

theorem proposition_4 {α : Type*} [Fintype α] [DecidableEq α] (Indep : Finset α → Prop)
    (h1 : IndepI1 Indep) (h2 : Axiom2 Indep) (h0 : Indep ∅) :
    ∀ (A : Finset α) (e : α),
      e ∈ spanOf Indep A ↔ e ∈ A ∨ ∃ C : Finset α, IsCircuit Indep C ∧ C \ A = {e} := by sorry

end EdmondsPartition.Main
