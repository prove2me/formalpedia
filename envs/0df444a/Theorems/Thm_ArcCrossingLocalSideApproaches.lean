-- Prove2me | Theorems.Thm_ArcCrossingLocalSideApproaches
-- name    : ArcCrossingLocalSideApproaches
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T20:46:00.038195+00:00
-- url     : https://prove2.me/theorems/c06b7193-1984-4c2a-b8ca-7a5a92e2770a
-- title:
--   Local side approaches for arc-crossing elimination
-- statement:
--   Assume a polygonal path has finitely many intersections with a polygonal arc, its vertices avoid the arc, and a polygonally path-connected bypass region supplies ordered local cuts around every crossing. Then the path can be replaced by a polygonal path with the same endpoints whose carrier avoids both the compact forbidden set and the arc. The replacement is assembled from safe original gaps and bypass-region detours.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/ArcCrossingLocalSideApproaches.lean#L1-L444

import Definitions.Def_PolygonalArc
import Definitions.Def_PolygonallyPathConnected

open Classical
noncomputable section

lemma ArcCrossingLocalSideApproaches
    (K : Set (EuclideanSpace ℝ (Fin 2))) (γ : PolygonalArc) (α : PolygonalPath)
    (W : Set (EuclideanSpace ℝ (Fin 2)))
    (cutBefore cutAfter :
      ∀ (i : ℕ), i + 1 < α.vertices.length →
        EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) :
    Set.Finite (α.carrier ∩ γ.carrier) →
      α.carrier ⊆ Kᶜ →
        α.source ∈ (K ∪ γ.carrier)ᶜ →
          α.target ∈ (K ∪ γ.carrier)ᶜ →
            W ⊆ (K ∪ γ.carrier)ᶜ →
              PolygonallyPathConnected W →
                (∀ v : EuclideanSpace ℝ (Fin 2), v ∈ α.vertices → v ∉ γ.carrier) →
                (∀ (i : ℕ) (hi : i + 1 < α.vertices.length)
                    (x : EuclideanSpace ℝ (Fin 2)),
                    x ∈ openSegment ℝ α.vertices[i] α.vertices[i + 1] →
                      x ∈ γ.carrier →
                        cutBefore i hi x ∈ openSegment ℝ α.vertices[i] x ∧
                          cutAfter i hi x ∈ openSegment ℝ x α.vertices[i + 1] ∧
                            cutBefore i hi x ∈ W ∧
                              cutAfter i hi x ∈ W ∧
                                segment ℝ (cutBefore i hi x) (cutAfter i hi x) ∩
                                    γ.carrier =
                                  {x}) →
                  (∀ (i : ℕ) (hi : i + 1 < α.vertices.length)
                      (x y : EuclideanSpace ℝ (Fin 2)),
                      x ∈ openSegment ℝ α.vertices[i] α.vertices[i + 1] →
                        y ∈ openSegment ℝ α.vertices[i] α.vertices[i + 1] →
                          x ∈ γ.carrier →
                            y ∈ γ.carrier →
                              x ≠ y →
                                Disjoint
                                  (segment ℝ (cutBefore i hi x) (cutAfter i hi x))
                                  (segment ℝ (cutBefore i hi y) (cutAfter i hi y))) →
                    (∀ (i : ℕ) (hi : i + 1 < α.vertices.length)
                        (y : EuclideanSpace ℝ (Fin 2)),
                        y ∈ segment ℝ α.vertices[i] α.vertices[i + 1] →
                          y ∈ γ.carrier →
                            ∃ x : EuclideanSpace ℝ (Fin 2),
                              x ∈ openSegment ℝ α.vertices[i] α.vertices[i + 1] ∧
                                x ∈ γ.carrier ∧
                                  y ∈ segment ℝ (cutBefore i hi x) (cutAfter i hi x)) →
                      ∃ α' : PolygonalPath,
                        α'.source = α.source ∧
                          α'.target = α.target ∧
                            α'.carrier ⊆ (K ∪ γ.carrier)ᶜ := by sorry
