-- Prove2me | Theorems.Thm_ArcCrossingBypassRegionData
-- name    : ArcCrossingBypassRegionData
-- status  : Open
-- author  : @xuanji
-- created : 2026-09-27T20:45:53.512675+00:00
-- url     : https://prove2.me/theorems/85fa75de-3c6a-4d34-9f5a-f8842e2e6d42
-- title:
--   Bypass-region data for arc-crossing elimination
-- statement:
--   Given a compact forbidden set, a polygonal arc, a finite polygonal presentation of that arc, and a polygonal path in general position whose only intersection with the arc is pendant at one endpoint, there is a connected bypass region in the complement. For every crossing of a path segment with the arc, the region supplies ordered cut points on the two sides of the crossing; the associated short segment meets the arc only at that crossing, distinct crossings give disjoint short segments, and every point of the original segment's arc intersection lies on one of these short segments.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/ArcCrossingBypassRegionData.lean#L1-L398

import Definitions.Def_PolygonalArc
import Definitions.Def_PolygonalPathInGeneralPosition
import Definitions.Def_PolygonallyPathConnected

open Classical
noncomputable section

lemma ArcCrossingBypassRegionData
    (K : Set (EuclideanSpace ℝ (Fin 2))) (γ : PolygonalArc)
    (Γ : FinitePolygonalSet) (α : PolygonalPath) :
    IsCompact K →
      Γ.carrier = γ.carrier →
        (∀ v : EuclideanSpace ℝ (Fin 2), v ∈ γ.vertices → v ∈ Γ.points) →
          α.carrier ⊆ Kᶜ →
            α.source ∈ (K ∪ γ.carrier)ᶜ →
              α.target ∈ (K ∪ γ.carrier)ᶜ →
                γ.source ∉ α.carrier →
                  γ.target ∉ α.carrier →
                    PolygonalPathInGeneralPosition α Γ →
                      ((γ.carrier ∩ K =
                          ({γ.source} : Set (EuclideanSpace ℝ (Fin 2))) ∧
                            γ.target ∉ K) ∨
                        (γ.carrier ∩ K =
                          ({γ.target} : Set (EuclideanSpace ℝ (Fin 2))) ∧
                            γ.source ∉ K)) →
                        (α.carrier ∩ γ.carrier).Nonempty →
                          ∃ (W : Set (EuclideanSpace ℝ (Fin 2)))
                            (cutBefore cutAfter :
                              ∀ (i : ℕ), i + 1 < α.vertices.length →
                                EuclideanSpace ℝ (Fin 2) →
                                  EuclideanSpace ℝ (Fin 2)),
                            W ⊆ (K ∪ γ.carrier)ᶜ ∧
                              PolygonallyPathConnected W ∧
                                (∀ (i : ℕ) (hi : i + 1 < α.vertices.length)
                                    (x : EuclideanSpace ℝ (Fin 2)),
                                    x ∈ openSegment ℝ α.vertices[i]
                                        α.vertices[i + 1] →
                                      x ∈ γ.carrier →
                                        cutBefore i hi x ∈
                                            openSegment ℝ α.vertices[i] x ∧
                                          cutAfter i hi x ∈
                                            openSegment ℝ x α.vertices[i + 1] ∧
                                            cutBefore i hi x ∈ W ∧
                                              cutAfter i hi x ∈ W ∧
                                                segment ℝ (cutBefore i hi x)
                                                    (cutAfter i hi x) ∩
                                                    γ.carrier =
                                                  {x}) ∧
                                  (∀ (i : ℕ) (hi : i + 1 < α.vertices.length)
                                      (x y : EuclideanSpace ℝ (Fin 2)),
                                      x ∈ openSegment ℝ α.vertices[i]
                                          α.vertices[i + 1] →
                                        y ∈ openSegment ℝ α.vertices[i]
                                            α.vertices[i + 1] →
                                          x ∈ γ.carrier →
                                            y ∈ γ.carrier →
                                              x ≠ y →
                                                Disjoint
                                                  (segment ℝ (cutBefore i hi x)
                                                    (cutAfter i hi x))
                                                  (segment ℝ (cutBefore i hi y)
                                                    (cutAfter i hi y))) ∧
                                    (∀ (i : ℕ) (hi : i + 1 < α.vertices.length)
                                        (y : EuclideanSpace ℝ (Fin 2)),
                                        y ∈ segment ℝ α.vertices[i]
                                            α.vertices[i + 1] →
                                          y ∈ γ.carrier →
                                            ∃ x : EuclideanSpace ℝ (Fin 2),
                                              x ∈ openSegment ℝ α.vertices[i]
                                                  α.vertices[i + 1] ∧
                                                x ∈ γ.carrier ∧
                                                  y ∈ segment ℝ (cutBefore i hi x)
                                                    (cutAfter i hi x)) := by sorry
