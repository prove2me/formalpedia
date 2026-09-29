-- Prove2me | Theorems.Thm_ArcCrossingCutWindowParameters
-- name    : ArcCrossingCutWindowParameters
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T20:55:29.144794+00:00
-- url     : https://prove2.me/theorems/1aeac975-86c4-4117-9dae-a84bad9baa78
-- title:
--   Arc-crossing cut window parameters
-- statement:
--   If a point in the interior of a polygonal path segment has two prescribed points approaching it from the two sides, then those points are represented by affine parameters strictly before and after the parameter of the intersection point.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/ArcCrossingCutWindowParameters.lean#L1-L68

import Definitions.Def_PolygonalPath

open Classical
noncomputable section

lemma ArcCrossingCutWindowParameters
    (α : PolygonalPath) (i : ℕ) (hi : i + 1 < α.vertices.length)
    (x before after : EuclideanSpace ℝ (Fin 2)) (p : ℝ) :
    0 < p →
      p < 1 →
        AffineMap.lineMap α.vertices[i] α.vertices[i + 1] p = x →
          before ∈ openSegment ℝ α.vertices[i] x →
            after ∈ openSegment ℝ x α.vertices[i + 1] →
              ∃ b a : ℝ,
                0 < b ∧ b < p ∧ p < a ∧ a < 1 ∧
                  AffineMap.lineMap α.vertices[i] α.vertices[i + 1] b = before ∧
                    AffineMap.lineMap α.vertices[i] α.vertices[i + 1] a = after := by sorry
