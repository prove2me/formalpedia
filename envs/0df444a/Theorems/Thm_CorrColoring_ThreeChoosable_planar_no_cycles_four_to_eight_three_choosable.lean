-- Prove2me | Theorems.Thm_CorrColoring_ThreeChoosable_planar_no_cycles_four_to_eight_three_choosable
-- name    : CorrColoring.ThreeChoosable.planar_no_cycles_four_to_eight_three_choosable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T01:08:36.107985+00:00
-- url     : https://prove2.me/theorems/8f6537b0-76fd-4284-a0f7-2870f319aa58
-- title:
--   Theorem 1 — every planar graph without cycles of lengths 4 to 8 is 3-choosable
-- statement:
--   Let $G$ be a finite simple planar graph that has no cycle of length 4, 5, 6, 7 or 8 (triangles and cycles of length at least 9 are allowed). Then
--
--   $$G \text{ is } 3\text{-choosable}:$$
--
--   for every assignment $L$ of lists of exactly three colours to the vertices of $G$, there is a proper colouring $\varphi$ of $G$ with $\varphi(v) \in L(v)$ for every vertex $v$.
--
--   This answers a question of Borodin, open for more than fifteen years, and is the headline result of Dvořák and Postle; it is proved by way of correspondence colouring (Theorem 6 and Lemma 5).
--
--   **Formalization Note** Planarity is the existence of a straight-line plane drawing, equivalent to planarity for finite simple graphs by Fáry's theorem. Colours come from an arbitrary type and lists are finite sets of cardinality exactly 3.
-- source:
--   Dvořák, Postle, Correspondence coloring and its application to list-coloring planar graphs without cycles of lengths 4 to 8, arXiv:1508.03437v2, p. 3, Theorem 1

import Mathlib
import Definitions.Def_CorrColoring_ThreeChoosable_IsChoosable
import Definitions.Def_CorrColoring_ThreeChoosable_NoCycleLengthsFourToEight
import Definitions.Def_CorrColoring_ThreeChoosable_StraightLineDrawing

namespace CorrColoring.ThreeChoosable

/-- Theorem 1 (Dvořák–Postle, p. 3). -/
theorem planar_no_cycles_four_to_eight_three_choosable {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : IsPlanar G) (hC : NoCycleLengthsFourToEight G) :
    IsChoosable G 3 := by sorry

end CorrColoring.ThreeChoosable
