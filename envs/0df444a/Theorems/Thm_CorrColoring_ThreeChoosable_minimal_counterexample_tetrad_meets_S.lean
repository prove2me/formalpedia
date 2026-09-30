-- Prove2me | Theorems.Thm_CorrColoring_ThreeChoosable_minimal_counterexample_tetrad_meets_S
-- name    : CorrColoring.ThreeChoosable.minimal_counterexample_tetrad_meets_S
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T01:06:57.008104+00:00
-- url     : https://prove2.me/theorems/b32f0674-f152-409a-8dfe-639a62d40c8a
-- title:
--   Lemma 12 — every tetrad of a minimal counterexample meets $S$
-- statement:
--   Let $B = (G, S, C, \varphi_0)$ be a minimal counterexample. Then for every tetrad $v_1 v_2 v_3 v_4$ of $G$,
--
--   $$\{v_1, v_2, v_3, v_4\} \cap S \neq \emptyset .$$
--
--   This is the main reduction of the proof of Theorem 8; it is the step where consistency on closed walks of length 3 is needed, and it bounds the number of consecutive light vertices on a face (Corollary 13), which feeds the discharging argument.
--
--   **Formalization Note** Tetrads are taken with respect to the fixed straight-line drawing of the target. As in the paper, the hypothesis describes a hypothetical object.
-- source:
--   Dvořák, Postle, Correspondence coloring and its application to list-coloring planar graphs without cycles of lengths 4 to 8, arXiv:1508.03437v2, p. 16, Lemma 12

import Mathlib
import Definitions.Def_CorrColoring_ThreeChoosable_Target
import Definitions.Def_CorrColoring_ThreeChoosable_IsTetrad

namespace CorrColoring.ThreeChoosable

/-- Lemma 12 (Dvořák–Postle, p. 16). -/
theorem minimal_counterexample_tetrad_meets_S (B : Target) (hB : B.IsMinimalCounterexample)
    (v₁ v₂ v₃ v₄ : B.V) (hT : IsTetrad B.D v₁ v₂ v₃ v₄) :
    v₁ ∈ B.S ∨ v₂ ∈ B.S ∨ v₃ ∈ B.S ∨ v₄ ∈ B.S := by sorry

end CorrColoring.ThreeChoosable
