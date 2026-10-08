-- Prove2me | Theorems.Thm_EdmondsPartition_Main_span_facts
-- name    : EdmondsPartition.Main.span_facts
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-06T15:23:44.614119+00:00
-- url     : https://prove2.me/theorems/25f18bc9-5fa6-4691-bab6-8554dc648481
-- title:
--   Spans: closure membership, span property and rank of S(J)
-- statement:
--   Throughout, $M$ is a finite matroid: a finite set of elements (the type $\alpha$) together with a family of *independent* subsets satisfying **Axiom 1** (every subset of an independent set is independent) and **Axiom 2** (for every subset $A$, all maximal independent subsets of $A$ have the same number of elements). The rank $r(A)$ is the largest cardinality of an independent subset of $A$. A *span* is a set $S$ such that no circuit (minimal dependent set) has exactly one element outside $S$, and $S(J)$ is the minimal span containing $J$ (the intersection of all spans containing $J$).
--
--   For every $J\subseteq M$:
--
--   1. an element $e$ lies in $S(J)$ if and only if $r(J\cup\{e\})=r(J)$;
--   2. $S(J)$ is itself a span;
--   3. $r(S(J))=r(J)$.
--
--   So the minimal span of $J$ is its rank closure. The proof shows that the rank closure is a span (a circuit with exactly one element $e$ outside the closure would force $e$ into the closure, by submodularity of the rank) and that it lies in every span containing $J$ (an element of the closure outside a span $S\supseteq J$ lies on a circuit meeting the complement of $S$ in one element).
--
--   **Formalization Note** Lean also assumes that the empty set is independent ($h_0$). Part 1 is stated as an equivalence over all $e$, including $e\in J$, for which both sides hold.
-- source:
--   J. Edmonds, Minimum partition of a matroid into independent subsets, J. Res. NBS 69B (1965), p. 69, §1.4, p. 69 (spans and their ranks)

import Mathlib
import Definitions.Def_WhitneyMatroid_RankIndep_Postulates
import Definitions.Def_EdmondsPartition_Main_Basic

namespace EdmondsPartition.Main

open WhitneyMatroid.RankIndep

theorem span_facts {α : Type*} [Fintype α] [DecidableEq α] (Indep : Finset α → Prop)
    (h1 : IndepI1 Indep) (h2 : Axiom2 Indep) (h0 : Indep ∅) (J : Finset α) :
    (∀ e : α, e ∈ spanOf Indep J ↔ rankOfIndep Indep (insert e J) = rankOfIndep Indep J) ∧
      IsSpan Indep (spanOf Indep J) ∧
      rankOfIndep Indep (spanOf Indep J) = rankOfIndep Indep J := by sorry

end EdmondsPartition.Main
