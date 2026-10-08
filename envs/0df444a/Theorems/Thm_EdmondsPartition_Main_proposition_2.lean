-- Prove2me | Theorems.Thm_EdmondsPartition_Main_proposition_2
-- name    : EdmondsPartition.Main.proposition_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T06:22:41.800578+00:00
-- url     : https://prove2.me/theorems/61c1fa65-dcb4-4278-89d6-dcf366d73ff6
-- title:
--   PROPOSITION 2, p. 70 — Axioms 1 and 2' are equivalent to the circuit axioms 1c and 2c
-- statement:
--   Let $M$ be a finite set. For a family $\mathcal C$ of subsets ("circuits"), Axiom 1c says no circuit contains a different circuit, and Axiom 2c says that if distinct circuits $C_1,C_2$ both contain an element $e$, then $(C_1\cup C_2)\setminus\{e\}$ contains a circuit. Starting from circuits, call a set independent when it contains no circuit.
--
--   1. If a family of independent sets satisfies Axioms 1 and 2', then its circuits (minimal dependent sets) satisfy Axioms 1c and 2c, and the sets containing none of these circuits are exactly the independent sets.
--   2. If a family $\mathcal C$ satisfies Axioms 1c and 2c, then the sets containing no member of $\mathcal C$ satisfy Axioms 1 and 2', and the minimal dependent sets of this system are exactly the members of $\mathcal C$.
--
--   Together the two translations are mutually inverse, so matroids can equally be axiomatized by their circuits.
--
--   **Formalization Note** Both directions are stated for arbitrary families of subsets of a finite type, with no non-emptiness assumption; for the empty independence family the circuits are $\{\emptyset\}$, and conversely.
-- source:
--   Edmonds, Minimum partition of a matroid into independent subsets, J. Res. NBS 69B (1965), p. 70, PROPOSITION 2 with AXIOMS 1c, 2c

import Mathlib
import Definitions.Def_WhitneyMatroid_RankIndep_Postulates
import Definitions.Def_EdmondsPartition_Main_Basic

namespace EdmondsPartition.Main

open WhitneyMatroid.RankIndep

theorem proposition_2 {α : Type*} [Fintype α] [DecidableEq α] :
    (∀ Indep : Finset α → Prop, IndepI1 Indep → Axiom2' Indep →
      Axiom1c (IsCircuit Indep) ∧ Axiom2c (IsCircuit Indep) ∧
        indepOfCircuits (IsCircuit Indep) = Indep) ∧
    (∀ Circ : Finset α → Prop, Axiom1c Circ → Axiom2c Circ →
      IndepI1 (indepOfCircuits Circ) ∧ Axiom2' (indepOfCircuits Circ) ∧
        IsCircuit (indepOfCircuits Circ) = Circ) := by sorry

end EdmondsPartition.Main
