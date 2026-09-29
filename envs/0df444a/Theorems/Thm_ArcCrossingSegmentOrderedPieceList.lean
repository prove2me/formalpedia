-- Prove2me | Theorems.Thm_ArcCrossingSegmentOrderedPieceList
-- name    : ArcCrossingSegmentOrderedPieceList
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T20:55:40.822427+00:00
-- url     : https://prove2.me/theorems/11805b31-e547-43f1-81f6-8612bdb0915b
-- title:
--   Arc-crossing ordered piece list
-- statement:
--   Ordered safe gaps, local detours, and boundary pieces along one polygonal path segment can be assembled into a finite chained list of polygonal paths from the segment start to its end.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/ArcCrossingSegmentOrderedPieceList.lean#L1-L267

import Definitions.Def_PolygonalArc
import Definitions.Def_PolygonalPath

open Classical
noncomputable section

lemma ArcCrossingSegmentOrderedPieceList
    (γ : PolygonalArc) (α : PolygonalPath)
    (Safe : Set (EuclideanSpace ℝ (Fin 2)))
    (i : ℕ) (hi : i + 1 < α.vertices.length)
    (params : List ℝ)
    (left right : (n : ℕ) → n < params.length → ℝ) :
    (∀ n (hn : n < params.length),
      0 < left n hn ∧ left n hn < params[n] ∧
        params[n] < right n hn ∧ right n hn < 1) →
      (∀ n (hn : n + 1 < params.length),
        right n (Nat.lt_of_succ_lt hn) < left (n + 1) hn) →
        (∀ n (hn : n + 1 < params.length) t,
          0 < t → t < 1 →
            AffineMap.lineMap α.vertices[i] α.vertices[i + 1] t ∈ γ.carrier →
              ¬ (params[n] < t ∧ t < params[n + 1])) →
          (∀ (hpos : 0 < params.length) u,
            u ∈ params → ¬ (0 ≤ u ∧ u ≤ left 0 hpos)) →
            (∀ (hpos : 0 < params.length) u,
              u ∈ params →
                ¬ (right (params.length - 1) (Nat.sub_lt hpos (by decide)) ≤ u ∧
                  u ≤ 1)) →
              (params = [] → ∀ u, u ∈ params → False) →
                (∀ s t : ℝ,
                  0 ≤ s →
                    s ≤ t →
                      t ≤ 1 →
                        (∀ u : ℝ, u ∈ params → ¬ (s ≤ u ∧ u ≤ t)) →
                          ∃ η : PolygonalPath,
                            η.source =
                                AffineMap.lineMap α.vertices[i] α.vertices[i + 1] s ∧
                              η.target =
                                  AffineMap.lineMap α.vertices[i] α.vertices[i + 1] t ∧
                                η.carrier ⊆ Safe) →
                  (∀ leftBound rightBound s t : ℝ,
                    leftBound < s →
                      s ≤ t →
                        t < rightBound →
                          0 < leftBound →
                            rightBound < 1 →
                              (∀ u : ℝ, 0 < u → u < 1 →
                                AffineMap.lineMap α.vertices[i] α.vertices[i + 1] u ∈
                                  γ.carrier →
                                  ¬ (leftBound < u ∧ u < rightBound)) →
                                ∃ η : PolygonalPath,
                                  η.source =
                                      AffineMap.lineMap α.vertices[i] α.vertices[i + 1]
                                        s ∧
                                    η.target =
                                        AffineMap.lineMap α.vertices[i] α.vertices[i + 1]
                                          t ∧
                                      η.carrier ⊆ Safe) →
                    (∀ n (hn : n < params.length),
                      ∃ η : PolygonalPath,
                        η.source =
                            AffineMap.lineMap α.vertices[i] α.vertices[i + 1]
                              (left n hn) ∧
                          η.target =
                              AffineMap.lineMap α.vertices[i] α.vertices[i + 1]
                                (right n hn) ∧
                            η.carrier ⊆ Safe) →
                      ∃ (pieces : List PolygonalPath) (first last : PolygonalPath),
                        pieces.head? = some first ∧
                          pieces.getLast? = some last ∧
                            first.source = α.vertices[i] ∧
                              last.target = α.vertices[i + 1] ∧
                                (∀ η : PolygonalPath, η ∈ pieces → η.carrier ⊆ Safe) ∧
                                  (∀ (j : ℕ) (hj : j + 1 < pieces.length),
                                    (pieces[j]).target = (pieces[j + 1]).source) := by sorry
