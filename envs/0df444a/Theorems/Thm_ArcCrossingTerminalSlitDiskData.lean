-- Prove2me | Theorems.Thm_ArcCrossingTerminalSlitDiskData
-- name    : ArcCrossingTerminalSlitDiskData
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T21:39:59.581225+00:00
-- url     : https://prove2.me/theorems/d4861095-b29a-4720-ae83-868973913d98
-- title:
--   Terminal slit-disk data at an arc endpoint
-- statement:
--   For an isolated polygonal tail endpoint and a positive separation from the old prefix, one can choose a slit-disk radius, a smaller terminal isolation radius, and a cone constant. The slit disk is open and connected, avoids the forbidden set, contains the terminal left cone and the corresponding reversed initial left cone, and preserves endpoint isolation.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/ArcCrossingTerminalSlitDiskData.lean#L1-425

import Definitions.Def_ArcCrossingEarlierPrefix
import Definitions.Def_PolygonalArc
import Definitions.Def_PolygonalArcEndpointIsolation
import Definitions.Def_PolygonalArcInitialEndpointLeftCone
import Definitions.Def_PolygonalArcReverse
import Definitions.Def_PolygonalArcTerminalEndpointLeftCone

open Classical
noncomputable section

lemma ArcCrossingTerminalSlitDiskData
    (K : Set (EuclideanSpace ℝ (Fin 2))) (δ τ : PolygonalArc)
    (j : ℕ) (c d : EuclideanSpace ℝ (Fin 2)) (r₀ r₁ η : ℝ)
    (hj : j + 1 < δ.vertices.length)
    (hcOpen : c ∈ openSegment ℝ δ.vertices[j] δ.vertices[j + 1])
    (hτvertices : τ.vertices = c :: δ.vertices.drop (j + 1))
    (hτtarget : τ.target = δ.target)
    (hIso : PolygonalArcEndpointIsolation τ r₀ r₁)
    (hηpos : 0 < η)
    (hηsep :
      ∀ a, a ∈
          (K ∪ (ArcCrossingEarlierPrefix δ j hj ∪ segment ℝ δ.vertices[j] d)) →
        ∀ b, b ∈ τ.carrier → η ≤ dist a b) :
    ∃ ρ rT K₁ : ℝ,
      0 < ρ ∧ 0 < rT ∧ rT < r₁ ∧ 0 < K₁ ∧
        (let hprev : τ.vertices.length - 2 < τ.vertices.length := by
            have hlen := τ.length_ge_two
            omega
         let base : EuclideanSpace ℝ (Fin 2) :=
            τ.vertices[τ.vertices.length - 2]'hprev - τ.target
         let ray : Set (EuclideanSpace ℝ (Fin 2)) :=
            {q | ∃ t : ℝ, 0 < t ∧ q = τ.target + t • base}
         let Dstar : Set (EuclideanSpace ℝ (Fin 2)) :=
            Metric.ball τ.target ρ \
              (ray ∪ ({τ.target} : Set (EuclideanSpace ℝ (Fin 2))))
         Dstar ⊆ (K ∪ δ.carrier)ᶜ) ∧
          (let hprev : τ.vertices.length - 2 < τ.vertices.length := by
              have hlen := τ.length_ge_two
              omega
           let base : EuclideanSpace ℝ (Fin 2) :=
              τ.vertices[τ.vertices.length - 2]'hprev - τ.target
           let ray : Set (EuclideanSpace ℝ (Fin 2)) :=
              {q | ∃ t : ℝ, 0 < t ∧ q = τ.target + t • base}
           let Dstar : Set (EuclideanSpace ℝ (Fin 2)) :=
              Metric.ball τ.target ρ \
                (ray ∪ ({τ.target} : Set (EuclideanSpace ℝ (Fin 2))))
           IsOpen Dstar) ∧
            (let hprev : τ.vertices.length - 2 < τ.vertices.length := by
                have hlen := τ.length_ge_two
                omega
             let base : EuclideanSpace ℝ (Fin 2) :=
                τ.vertices[τ.vertices.length - 2]'hprev - τ.target
             let ray : Set (EuclideanSpace ℝ (Fin 2)) :=
                {q | ∃ t : ℝ, 0 < t ∧ q = τ.target + t • base}
             let Dstar : Set (EuclideanSpace ℝ (Fin 2)) :=
                Metric.ball τ.target ρ \
                  (ray ∪ ({τ.target} : Set (EuclideanSpace ℝ (Fin 2))))
             IsConnected Dstar) ∧
              PolygonalArcEndpointIsolation τ r₀ rT ∧
                (let hprev : τ.vertices.length - 2 < τ.vertices.length := by
                    have hlen := τ.length_ge_two
                    omega
                 let base : EuclideanSpace ℝ (Fin 2) :=
                    τ.vertices[τ.vertices.length - 2]'hprev - τ.target
                 let ray : Set (EuclideanSpace ℝ (Fin 2)) :=
                    {q | ∃ t : ℝ, 0 < t ∧ q = τ.target + t • base}
                 let Dstar : Set (EuclideanSpace ℝ (Fin 2)) :=
                    Metric.ball τ.target ρ \
                      (ray ∪ ({τ.target} : Set (EuclideanSpace ℝ (Fin 2))))
                 PolygonalArcTerminalEndpointLeftCone τ rT K₁ ⊆ Dstar) ∧
                  (let hprev : τ.vertices.length - 2 < τ.vertices.length := by
                      have hlen := τ.length_ge_two
                      omega
                   let base : EuclideanSpace ℝ (Fin 2) :=
                      τ.vertices[τ.vertices.length - 2]'hprev - τ.target
                   let ray : Set (EuclideanSpace ℝ (Fin 2)) :=
                      {q | ∃ t : ℝ, 0 < t ∧ q = τ.target + t • base}
                   let Dstar : Set (EuclideanSpace ℝ (Fin 2)) :=
                      Metric.ball τ.target ρ \
                        (ray ∪ ({τ.target} : Set (EuclideanSpace ℝ (Fin 2))))
                   PolygonalArcInitialEndpointLeftCone (PolygonalArcReverse τ) rT K₁ ⊆
                    Dstar) := by sorry
