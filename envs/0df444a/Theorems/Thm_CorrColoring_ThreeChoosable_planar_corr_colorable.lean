-- Prove2me | Theorems.Thm_CorrColoring_ThreeChoosable_planar_corr_colorable
-- name    : CorrColoring.ThreeChoosable.planar_corr_colorable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T01:08:06.707804+00:00
-- url     : https://prove2.me/theorems/d267a9f9-c00e-48bb-a144-3696966011e5
-- title:
--   Theorem 6 — planar graphs without cycles of lengths 4 to 8 are $C$-colorable for 3-correspondence assignments consistent on triangles
-- statement:
--   Let $G$ be a finite planar graph without cycles of lengths 4 to 8. Then for every 3-correspondence assignment $C$ for $G$ that is consistent on every closed walk of length 3 in $G$,
--
--   $$G \text{ is } C\text{-colorable}.$$
--
--   By Lemma 5 this implies that such graphs are 3-choosable (Theorem 1). Whether the consistency hypothesis can be dropped (correspondence chromatic number at most 3) is left open in the paper.
--
--   **Formalization Note** Planarity is the existence of a straight-line plane drawing (Fáry's theorem). A closed walk of length 3 in a simple graph traverses a triangle.
-- source:
--   Dvořák, Postle, Correspondence coloring and its application to list-coloring planar graphs without cycles of lengths 4 to 8, arXiv:1508.03437v2, p. 7, Theorem 6

import Mathlib
import Definitions.Def_CorrColoring_ThreeChoosable_NoCycleLengthsFourToEight
import Definitions.Def_CorrColoring_ThreeChoosable_StraightLineDrawing
import Definitions.Def_CorrColoring_ThreeChoosable_KCorrAssignment
import Definitions.Def_CorrColoring_ThreeChoosable_ConsistentOn

namespace CorrColoring.ThreeChoosable

/-- Theorem 6 (Dvořák–Postle, p. 7). -/
theorem planar_corr_colorable {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : IsPlanar G) (hC : NoCycleLengthsFourToEight G)
    (C : KCorrAssignment G 3) (hcons : ConsistentOnTriangles C) :
    ∃ φ : V → Fin 3, IsCColoring C φ := by sorry

end CorrColoring.ThreeChoosable
