-- Prove2me | Theorems.Thm_ArcCrossingTailSourcePrefixData
-- name    : ArcCrossingTailSourcePrefixData
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T21:39:34.269482+00:00
-- url     : https://prove2.me/theorems/e26485dd-e5cd-4d71-a326-9b94901b414f
-- title:
--   Source-prefix and separation data for an arc tail
-- statement:
--   For a compact forbidden set and a tail arc beginning at an interior point of the first crossing segment, one can choose endpoint-isolation radii, an auxiliary point \(d\), and a positive separation \(\eta\). The resulting old prefix together with \(K\) is compact and disjoint from the tail, while every point in the two sets is at least \(\eta\) from every tail point.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/ArcCrossingTailSourcePrefixData.lean#L1-206

import Definitions.Def_ArcCrossingEarlierPrefix
import Definitions.Def_PolygonalArc
import Definitions.Def_PolygonalArcEndpointIsolation

open Classical
noncomputable section

lemma ArcCrossingTailSourcePrefixData
    (K : Set (EuclideanSpace ℝ (Fin 2))) (δ τ : PolygonalArc)
    (j : ℕ) (c : EuclideanSpace ℝ (Fin 2))
    (hK : IsCompact K)
    (hj : j + 1 < δ.vertices.length)
    (hcOpen : c ∈ openSegment ℝ δ.vertices[j] δ.vertices[j + 1])
    (hτvertices : τ.vertices = c :: δ.vertices.drop (j + 1))
    (hτKdisjoint : Disjoint τ.carrier K) :
    ∃ (r₀ r₁ : ℝ) (d : EuclideanSpace ℝ (Fin 2)) (η : ℝ),
      PolygonalArcEndpointIsolation τ r₀ r₁ ∧
        d ∈ openSegment ℝ δ.vertices[j] c ∧
          dist c d < r₀ ∧
            segment ℝ d c ⊆ Metric.ball c r₀ ∧
              segment ℝ d c ⊆ segment ℝ c δ.vertices[j] ∧
                IsCompact
                  (K ∪ (ArcCrossingEarlierPrefix δ j hj ∪ segment ℝ δ.vertices[j] d)) ∧
                  Disjoint
                    (K ∪ (ArcCrossingEarlierPrefix δ j hj ∪ segment ℝ δ.vertices[j] d))
                    τ.carrier ∧
                    0 < η ∧
                      ∀ a, a ∈
                          (K ∪ (ArcCrossingEarlierPrefix δ j hj ∪ segment ℝ δ.vertices[j] d)) →
                        ∀ b, b ∈ τ.carrier → η ≤ dist a b := by sorry
