-- Prove2me | Theorems.Thm_EdmondsPartition_Main_span_inter_rank_lt
-- name    : EdmondsPartition.Main.span_inter_rank_lt
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T06:25:58.266977+00:00
-- url     : https://prove2.me/theorems/27b01914-1de1-4754-8995-32e8ee1092fc
-- title:
--   §1.6, proof of THEOREM 1, p. 71 — rank drop: S(I ∩ S) ⊆ S and r(S(I ∩ S)) < r(S)
-- statement:
--   Throughout, $M$ is a finite matroid: a finite set of elements (the type $\alpha$, with $M$ the whole set) together with a family of *independent* subsets satisfying **Axiom 1** (every subset of an independent set is independent) and **Axiom 2** (for every subset $A$, all maximal independent subsets of $A$ have the same number of elements). For $A\subseteq M$, the rank $r(A)$ is the largest cardinality of an independent subset of $A$. A span is a set $S$ such that no circuit (minimal dependent set) has exactly one element outside $S$, and $S(A)$ is the minimal span containing $A$. Let $S$ be a span and $I$ an independent set with $|I\cap S|<r(S)$. Then
--   $$S(I\cap S)\subseteq S\qquad\text{and}\qquad r\bigl(S(I\cap S)\bigr)<r(S).$$
--
--   In the main proof this is the step $S_{i+1}=S(I_{i+1}\cap S_i)$ with $r(S_{i+1})<r(S_i)$, which makes the chain of spans $S_1\supseteq S_2\supseteq\cdots$ strictly decrease in rank and hence terminate.
--
--   **Formalization Note** Lean also assumes that the empty set is independent ($h_0$). The paper's rank, "the number of elements in each maximal independent set contained in $A$", presupposes that every set has an independent subset; with an empty family Axioms 1 and 2 hold vacuously and the statement fails.
-- source:
--   Edmonds, Minimum partition of a matroid into independent subsets, J. Res. NBS 69B (1965), p. 71, §1.6, proof of THEOREM 1 ("Where S_{i+1} = S(I_{i+1} ∩ S_i), we have r(S_{i+1}) < r(S_i)"; "By construction, S₁ ⊃ S₂ ⊃ … ⊃ S_h")

import Mathlib
import Definitions.Def_WhitneyMatroid_RankIndep_Postulates
import Definitions.Def_EdmondsPartition_Main_Basic

namespace EdmondsPartition.Main

open WhitneyMatroid.RankIndep

theorem span_inter_rank_lt {α : Type*} [Fintype α] [DecidableEq α] (Indep : Finset α → Prop)
    (h1 : IndepI1 Indep) (h2 : Axiom2 Indep) (h0 : Indep ∅)
    (S I : Finset α) (hS : IsSpan Indep S) (hI : Indep I)
    (hlt : ((I ∩ S).card : ℤ) < rankOfIndep Indep S) :
    spanOf Indep (I ∩ S) ⊆ S ∧ rankOfIndep Indep (spanOf Indep (I ∩ S)) < rankOfIndep Indep S := by sorry

end EdmondsPartition.Main
