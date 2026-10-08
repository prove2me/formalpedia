-- Prove2me | Theorems.Thm_EdmondsPartition_Main_proposition_3
-- name    : EdmondsPartition.Main.proposition_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T06:22:57.770979+00:00
-- url     : https://prove2.me/theorems/5dad92d6-7f60-41a8-bc04-bd405cb454b4
-- title:
--   PROPOSITION 3 (Lehman), p. 70 — strong circuit elimination: a ∈ C ⊆ C₁ ∪ C₂ − e
-- statement:
--   Let $\mathcal C$ be a family of subsets ("circuits") of a finite set satisfying Axiom 1c (no circuit contains a different circuit) and Axiom 2c (if distinct circuits $C_1,C_2$ both contain $e$, then $(C_1\cup C_2)\setminus\{e\}$ contains a circuit). If $C_1, C_2$ are circuits with an element $e\in C_1\cap C_2$ and an element $a\in C_1\setminus C_2$, then there is a circuit $C$ with
--   $$a\in C\subseteq (C_1\cup C_2)\setminus\{e\}.$$
--
--   This strengthening of Axiom 2c, due to Lehman, controls which element the eliminated circuit keeps; it is used in the proof of PROPOSITION 4.
--
--   **Formalization Note** The page states the result for the circuits of a matroid, but its proof assumes only Axioms 1c and 2c, so it is stated for any circuit family satisfying them; the matroid form follows by PROPOSITION 2. Edmonds writes $\subset$ for inclusion, rendered here as $\subseteq$.
-- source:
--   Edmonds, Minimum partition of a matroid into independent subsets, J. Res. NBS 69B (1965), p. 70, PROPOSITION 3 (Lehman)

import Mathlib
import Definitions.Def_WhitneyMatroid_RankIndep_Postulates
import Definitions.Def_EdmondsPartition_Main_Basic

namespace EdmondsPartition.Main

open WhitneyMatroid.RankIndep

theorem proposition_3 {α : Type*} [Fintype α] [DecidableEq α]
    (Circ : Finset α → Prop) (h1c : Axiom1c Circ) (h2c : Axiom2c Circ) :
    ∀ (C₁ C₂ : Finset α) (e a : α), Circ C₁ → Circ C₂ → e ∈ C₁ → e ∈ C₂ → a ∈ C₁ → a ∉ C₂ →
      ∃ C : Finset α, Circ C ∧ a ∈ C ∧ C ⊆ (C₁ ∪ C₂).erase e := by sorry

end EdmondsPartition.Main
