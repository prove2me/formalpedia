-- Prove2me | Theorems.Thm_ArcCrossingSegmentParameterGapPiece
-- name    : ArcCrossingSegmentParameterGapPiece
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T20:55:25.149313+00:00
-- url     : https://prove2.me/theorems/0bd2c9b8-1d90-4c43-97c8-330ae88f18f5
-- title:
--   Arc-crossing segment parameter gap piece
-- statement:
--   A parameter interval lying strictly between consecutive intersection parameters on a polygonal path segment can be replaced by a polygonal path with the same endpoints that avoids both the forbidden set and the polygonal arc.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/ArcCrossingSegmentParameterGapPiece.lean#L1-L76

import Definitions.Def_PolygonalArc
import Definitions.Def_PolygonalPath

open Classical
noncomputable section

lemma ArcCrossingSegmentParameterGapPiece
    (K : Set (EuclideanSpace ℝ (Fin 2))) (γ : PolygonalArc) (α : PolygonalPath)
    (i : ℕ) (hi : i + 1 < α.vertices.length) (left right s t : ℝ) :
    α.carrier ⊆ Kᶜ →
      left < s →
        s ≤ t →
          t < right →
            0 < left →
              right < 1 →
                (∀ u : ℝ, 0 < u → u < 1 →
                  (AffineMap.lineMap α.vertices[i] α.vertices[i + 1]) u ∈ γ.carrier →
                    ¬ (left < u ∧ u < right)) →
                  ∃ η : PolygonalPath,
                    η.source =
                        (AffineMap.lineMap α.vertices[i] α.vertices[i + 1]) s ∧
                      η.target =
                        (AffineMap.lineMap α.vertices[i] α.vertices[i + 1]) t ∧
                        η.carrier ⊆ (K ∪ γ.carrier)ᶜ := by sorry
