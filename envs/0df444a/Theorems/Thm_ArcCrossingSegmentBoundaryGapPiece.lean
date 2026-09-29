-- Prove2me | Theorems.Thm_ArcCrossingSegmentBoundaryGapPiece
-- name    : ArcCrossingSegmentBoundaryGapPiece
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T20:55:21.257077+00:00
-- url     : https://prove2.me/theorems/e26fd183-a3d6-43c8-97aa-fefb8d3ed494
-- title:
--   Arc-crossing segment boundary gap piece
-- statement:
--   A closed parameter interval in a polygonal path segment containing no intersection with the polygonal arc, including possible endpoints, admits a safe polygonal replacement joining its affine endpoints.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/ArcCrossingSegmentBoundaryGapPiece.lean#L1-L81

import Definitions.Def_PolygonalArc
import Definitions.Def_PolygonalPath

open Classical
noncomputable section

lemma ArcCrossingSegmentBoundaryGapPiece
    (K : Set (EuclideanSpace ℝ (Fin 2))) (γ : PolygonalArc) (α : PolygonalPath)
    (i : ℕ) (hi : i + 1 < α.vertices.length) (s t : ℝ) :
    α.carrier ⊆ Kᶜ →
      0 ≤ s →
        s ≤ t →
          t ≤ 1 →
            α.vertices[i] ∉ γ.carrier →
              α.vertices[i + 1] ∉ γ.carrier →
                (∀ u : ℝ, 0 < u → u < 1 →
                  (AffineMap.lineMap α.vertices[i] α.vertices[i + 1]) u ∈ γ.carrier →
                    ¬ (s ≤ u ∧ u ≤ t)) →
                  ∃ η : PolygonalPath,
                    η.source =
                        (AffineMap.lineMap α.vertices[i] α.vertices[i + 1]) s ∧
                      η.target =
                        (AffineMap.lineMap α.vertices[i] α.vertices[i + 1]) t ∧
                        η.carrier ⊆ (K ∪ γ.carrier)ᶜ := by sorry
