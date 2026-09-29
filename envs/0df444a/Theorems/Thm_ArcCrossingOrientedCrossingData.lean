-- Prove2me | Theorems.Thm_ArcCrossingOrientedCrossingData
-- name    : ArcCrossingOrientedCrossingData
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T21:39:45.914294+00:00
-- url     : https://prove2.me/theorems/db670d38-9ea3-4c1d-a3e3-821d813abe9b
-- title:
--   Orientation normalization for an endpoint crossing
-- statement:
--   Under general position and the hypothesis that the compact set meets the arc only at one endpoint, either the given orientation already has the source as the attached endpoint or the reversed arc does. The theorem returns an oriented arc \(\delta\) with the same carrier and relative interior, listed vertices, finite path intersection, endpoint avoidance, and
--
--   $$\delta\cap K=\{\delta_{\mathrm{source}}\}.$$
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/ArcCrossingOrientedCrossingData.lean#L1-57

import Definitions.Def_PolygonalPathInGeneralPosition
import Definitions.Def_PolygonalArcReverse

open Classical
noncomputable section

lemma ArcCrossingOrientedCrossingData
    (K : Set (EuclideanSpace ℝ (Fin 2))) (γ : PolygonalArc)
    (Γ : FinitePolygonalSet) (α : PolygonalPath) :
    Γ.carrier = γ.carrier →
      (∀ v : EuclideanSpace ℝ (Fin 2), v ∈ γ.vertices → v ∈ Γ.points) →
        γ.source ∉ α.carrier →
          γ.target ∉ α.carrier →
            PolygonalPathInGeneralPosition α Γ →
              ((γ.carrier ∩ K =
                  ({γ.source} : Set (EuclideanSpace ℝ (Fin 2))) ∧
                    γ.target ∉ K) ∨
                (γ.carrier ∩ K =
                  ({γ.target} : Set (EuclideanSpace ℝ (Fin 2))) ∧
                    γ.source ∉ K)) →
                ∃ δ : PolygonalArc,
                  δ.carrier = γ.carrier ∧
                    δ.relativeInterior = γ.relativeInterior ∧
                      (∀ v : EuclideanSpace ℝ (Fin 2),
                        v ∈ δ.vertices → v ∈ Γ.points) ∧
                        (∀ v : EuclideanSpace ℝ (Fin 2),
                          v ∈ δ.vertices → v ∉ α.carrier) ∧
                          Set.Finite (α.carrier ∩ δ.carrier) ∧
                            δ.source ∉ α.carrier ∧
                              δ.target ∉ α.carrier ∧
                                δ.carrier ∩ K =
                                  ({δ.source} : Set (EuclideanSpace ℝ (Fin 2))) ∧
                                  δ.target ∉ K := by sorry
