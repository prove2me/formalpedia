-- Prove2me | Theorems.Thm_EdmondsPartition_Main_proposition_1
-- name    : EdmondsPartition.Main.proposition_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T06:22:42.954902+00:00
-- url     : https://prove2.me/theorems/6bd3ac9d-5551-4ce7-8200-e8a084346683
-- title:
--   PROPOSITION 1, p. 70 — Axioms 1 and 2' are equivalent to Axioms 1 and 2
-- statement:
--   Let $M$ be a finite set and let a family of subsets of $M$ be called independent. Axiom 1 says that every subset of an independent set is independent; Axiom 2 says that for every $A\subseteq M$ all maximal independent subsets of $A$ have the same cardinality; Axiom 2' says that for every independent set $I$ and element $e$, the set $I\cup\{e\}$ contains at most one circuit (minimal dependent set). Then
--   $$\text{Axiom 1}\wedge\text{Axiom 2}\iff\text{Axiom 1}\wedge\text{Axiom 2'}.$$
--
--   This lets the proof of THEOREM 1 work with Axiom 2', a statement about circuits, instead of the cardinality axiom that defines a matroid.
--
--   **Formalization Note** No other hypothesis is assumed: the statement is for an arbitrary family of subsets of a finite type, including the empty family (for which both sides hold).
-- source:
--   Edmonds, Minimum partition of a matroid into independent subsets, J. Res. NBS 69B (1965), p. 70, PROPOSITION 1

import Mathlib
import Definitions.Def_WhitneyMatroid_RankIndep_Postulates
import Definitions.Def_EdmondsPartition_Main_Basic

namespace EdmondsPartition.Main

open WhitneyMatroid.RankIndep

theorem proposition_1 {α : Type*} [Fintype α] [DecidableEq α]
    (Indep : Finset α → Prop) :
    (IndepI1 Indep ∧ Axiom2 Indep) ↔ (IndepI1 Indep ∧ Axiom2' Indep) := by sorry

end EdmondsPartition.Main
