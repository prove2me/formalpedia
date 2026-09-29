-- Prove2me | Theorems.Thm_FinitePolygonalPerturbation
-- name    : FinitePolygonalPerturbation
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T19:57:21.465265+00:00
-- url     : https://prove2.me/theorems/8560583b-6490-4e68-8fe0-fd27138c3714
-- title:
--   Perturbation of a polygonal path in general position
-- statement:
--   Let K be a finite polygonal set, U an open subset of the plane, γ a polygonal path contained in U with both endpoints outside K, A a compact set disjoint from U, and δ>0. Then γ can be perturbed to a polygonal path γ' with the same endpoints, still contained in U, lying within δ of γ, in general position with respect to K, and disjoint from A. This is the finite-avoidance perturbation principle used to put paths into controlled geometric position.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/FinitePolygonalPerturbation.lean#L1-L34

import Definitions.Def_PolygonalPathInGeneralPosition

open Classical
noncomputable section

lemma FinitePolygonalPerturbation (K : FinitePolygonalSet)
    (U : Set (EuclideanSpace ℝ (Fin 2))) (γ : PolygonalPath)
    (A : Set (EuclideanSpace ℝ (Fin 2))) (δ : ℝ) :
    IsOpen U →
      γ.carrier ⊆ U →
        γ.source ∈ U \ K.carrier →
          γ.target ∈ U \ K.carrier →
            0 < δ →
              IsCompact A →
                A ⊆ Uᶜ →
                  ∃ γ' : PolygonalPath,
                    γ'.source = γ.source ∧
                      γ'.target = γ.target ∧
                        γ'.carrier ⊆ U ∧
                          γ'.carrier ⊆
                            {p : EuclideanSpace ℝ (Fin 2) |
                              ∃ q : EuclideanSpace ℝ (Fin 2), q ∈ γ.carrier ∧ dist p q < δ} ∧
                            PolygonalPathInGeneralPosition γ' K ∧
                              Disjoint γ'.carrier A := by sorry
