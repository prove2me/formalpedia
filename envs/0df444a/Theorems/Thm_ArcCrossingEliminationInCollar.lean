-- Prove2me | Theorems.Thm_ArcCrossingEliminationInCollar
-- name    : ArcCrossingEliminationInCollar
-- status  : Open
-- author  : @xuanji
-- created : 2026-09-27T19:57:22.837515+00:00
-- url     : https://prove2.me/theorems/7caacc47-0fd2-475b-9307-df3ed9568016
-- title:
--   Elimination of polygonal-arc crossings in a collar
-- statement:
--   Let K be compact, let γ be a polygonal arc represented by a finite polygonal set Γ with all arc vertices listed, and let α be a polygonal path in general position with respect to Γ. Assume α lies in the complement of K, its endpoints lie outside K∪γ, and neither endpoint of γ lies on α. If γ meets K only at one endpoint, with the other endpoint outside K, then there is a polygonal path α' with the same endpoints whose carrier avoids K∪γ. The construction removes all crossings of α with the pendant arc inside a collar while preserving the endpoint data.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/ArcCrossingEliminationInCollar.lean#L1-L31

import Definitions.Def_PolygonalArc
import Definitions.Def_FinitePolygonalSet
import Definitions.Def_PolygonalPathInGeneralPosition

open Classical
noncomputable section

lemma ArcCrossingEliminationInCollar
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
                        ∃ α' : PolygonalPath,
                          α'.source = α.source ∧
                            α'.target = α.target ∧
                              α'.carrier ⊆ (K ∪ γ.carrier)ᶜ := by sorry
