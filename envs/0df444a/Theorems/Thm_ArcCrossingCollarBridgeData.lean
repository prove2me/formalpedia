-- Prove2me | Theorems.Thm_ArcCrossingCollarBridgeData
-- name    : ArcCrossingCollarBridgeData
-- status  : Open
-- author  : @xuanji
-- created : 2026-09-27T21:39:29.09996+00:00
-- url     : https://prove2.me/theorems/7cd2221d-59f1-4238-8642-32e7b7526f42
-- title:
--   Collar bridge data for an oriented arc tail
-- statement:
--   Given the compact forbidden set and an oriented polygonal tail with an isolated initial endpoint, an earlier-prefix cover, endpoint cones, and a terminal slit disk, the collar construction produces side-strip data \(S\) and a connected open bypass region \(W\). In particular,
--
--   $$W=S_{\mathrm{left}}\cup S_{\mathrm{right}}\cup D^*$$
--
--   and the two strips cover the collar away from the tail relative interior while avoiding the forbidden set.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/ArcCrossingCollarBridgeData.lean#L1-370

import Definitions.Def_ArcCrossingEarlierPrefix
import Definitions.Def_PolygonalArc
import Definitions.Def_PolygonalArcEndpointIsolation
import Definitions.Def_PolygonalArcInitialEndpointLeftCone
import Definitions.Def_PolygonalArcReverse
import Definitions.Def_PolygonalArcTerminalEndpointLeftCone
import Definitions.Def_PolygonalSideStrips
import Definitions.Def_PolygonallyPathConnected

open Classical
noncomputable section

set_option maxHeartbeats 1200000

lemma ArcCrossingCollarBridgeData
    (K Dstar : Set (EuclideanSpace ℝ (Fin 2))) (δ τ : PolygonalArc)
    (j : ℕ) (c d : EuclideanSpace ℝ (Fin 2)) (r₀ rT K₁ η : ℝ)
    (hj : j + 1 < δ.vertices.length)
    (hcOpen : c ∈ openSegment ℝ δ.vertices[j] δ.vertices[j + 1])
    (hτvertices : τ.vertices = c :: δ.vertices.drop (j + 1))
    (hτsource : τ.source = c)
    (hIso : PolygonalArcEndpointIsolation τ r₀ rT)
    (hK₁pos : 0 < K₁)
    (hnear_germ_ball : segment ℝ d c ⊆ Metric.ball c r₀)
    (hnear_germ_negative : segment ℝ d c ⊆ segment ℝ c δ.vertices[j])
    (hηpos : 0 < η)
    (hηsep :
      ∀ a, a ∈
          (K ∪ (ArcCrossingEarlierPrefix δ j hj ∪ segment ℝ δ.vertices[j] d)) →
        ∀ b, b ∈ τ.carrier → η ≤ dist a b)
    (hcarrier_cover :
      δ.carrier ⊆
        (ArcCrossingEarlierPrefix δ j hj ∪ segment ℝ δ.vertices[j] d) ∪
          segment ℝ d c ∪ τ.carrier)
    (hDstar_subset : Dstar ⊆ (K ∪ δ.carrier)ᶜ)
    (hDstar_open : IsOpen Dstar)
    (hDstar_connected : IsConnected Dstar)
    (hterminalLeftCone_Dstar :
      PolygonalArcTerminalEndpointLeftCone τ rT K₁ ⊆ Dstar)
    (hterminalRightCone_Dstar :
      PolygonalArcInitialEndpointLeftCone (PolygonalArcReverse τ) rT K₁ ⊆
        Dstar) :
    ∃ (S : PolygonalSideStrips τ) (W : Set (EuclideanSpace ℝ (Fin 2))),
      W = S.leftStrip ∪ S.rightStrip ∪ Dstar ∧
        W ⊆ (K ∪ δ.carrier)ᶜ ∧
          IsOpen W ∧
            IsConnected W ∧
              PolygonallyPathConnected W ∧
                (Dstar ∩ S.leftStrip).Nonempty ∧
                  (Dstar ∩ S.rightStrip).Nonempty ∧
                    S.leftStrip ⊆ W ∧
                      S.rightStrip ⊆ W ∧
                        τ.relativeInterior ⊆ S.collar ∧
                          IsOpen S.collar ∧
                            S.collar \ τ.relativeInterior =
                              S.leftStrip ∪ S.rightStrip := by sorry
