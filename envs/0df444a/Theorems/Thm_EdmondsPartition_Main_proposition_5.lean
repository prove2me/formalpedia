-- Prove2me | Theorems.Thm_EdmondsPartition_Main_proposition_5
-- name    : EdmondsPartition.Main.proposition_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T06:24:20.900359+00:00
-- url     : https://prove2.me/theorems/dcb5385d-bc59-461f-83c2-6720d645d459
-- title:
--   PROPOSITION 5, p. 70 — S(A) is the maximal set containing A of the same rank; r(S(I)) = |I| for independent I
-- statement:
--   Throughout, $M$ is a finite matroid: a finite set of elements (the type $\alpha$, with $M$ the whole set) together with a family of *independent* subsets satisfying **Axiom 1** (every subset of an independent set is independent) and **Axiom 2** (for every subset $A$, all maximal independent subsets of $A$ have the same number of elements). For $A\subseteq M$, the rank $r(A)$ is the largest cardinality of an independent subset of $A$. The span $S(A)$ is the minimal set containing $A$ such that no circuit (minimal dependent set) has exactly one element outside it. Then:
--
--   1. for every $A\subseteq M$, $S(A)$ is the unique maximal set containing $A$ with the same rank as $A$: $A\subseteq S(A)$, $r(S(A))=r(A)$, and every $T\supseteq A$ with $r(T)=r(A)$ satisfies $T\subseteq S(A)$;
--   2. in particular, for every independent set $I$,
--   $$r\bigl(S(I)\bigr)=|I|.$$
--
--   Besides Axioms 1 and 2' and the definitions of circuit and span, the second part is the only fact about matroids used in the proof of THEOREM 1.
--
--   **Formalization Note** Lean also assumes that the empty set is independent ($h_0$). The paper's rank, "the number of elements in each maximal independent set contained in $A$", presupposes that every set has an independent subset; with an empty family Axioms 1 and 2 hold vacuously and the statement fails.
-- source:
--   Edmonds, Minimum partition of a matroid into independent subsets, J. Res. NBS 69B (1965), p. 70, PROPOSITION 5 (with its "In particular" sentence)

import Mathlib
import Definitions.Def_WhitneyMatroid_RankIndep_Postulates
import Definitions.Def_EdmondsPartition_Main_Basic

namespace EdmondsPartition.Main

open WhitneyMatroid.RankIndep

theorem proposition_5 {α : Type*} [Fintype α] [DecidableEq α] (Indep : Finset α → Prop)
    (h1 : IndepI1 Indep) (h2 : Axiom2 Indep) (h0 : Indep ∅) :
    (∀ A : Finset α, A ⊆ spanOf Indep A ∧
        rankOfIndep Indep (spanOf Indep A) = rankOfIndep Indep A ∧
        ∀ T : Finset α, A ⊆ T → rankOfIndep Indep T = rankOfIndep Indep A →
          T ⊆ spanOf Indep A) ∧
      ∀ I : Finset α, Indep I → rankOfIndep Indep (spanOf Indep I) = (I.card : ℤ) := by sorry

end EdmondsPartition.Main
