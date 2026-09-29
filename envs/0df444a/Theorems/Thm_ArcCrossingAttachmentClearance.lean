-- Prove2me | Theorems.Thm_ArcCrossingAttachmentClearance
-- name    : ArcCrossingAttachmentClearance
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T21:39:09.684464+00:00
-- url     : https://prove2.me/theorems/d4fa4e43-0a77-4674-822e-78bae35a1317
-- title:
--   Attachment clearance away from an endpoint
-- statement:
--   For a polygonal arc \(\gamma\), path \(\alpha\), compact set \(K\), and point \(a\), assume that \(a\) is not on \(\alpha\), the finite intersection \(\alpha\cap\gamma\) is nonempty, and \(\gamma\cap K=\{a\}\). Then there is a positive radius \(\varepsilon\) such that every intersection point is at distance at least \(\varepsilon\) from \(a\), the arc tail outside that radius is compact, and that tail is disjoint from \(K\). This gives quantitative clearance for the crossing construction.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/ArcCrossingAttachmentClearance.lean#L1-53

import Definitions.Def_PolygonalArc
import Definitions.Def_PolygonalPath

open Classical
noncomputable section

lemma ArcCrossingAttachmentClearance
    (K : Set (EuclideanSpace ℝ (Fin 2))) (γ : PolygonalArc) (α : PolygonalPath)
    (a : EuclideanSpace ℝ (Fin 2)) :
    a ∉ α.carrier →
      Set.Finite (α.carrier ∩ γ.carrier) →
        (α.carrier ∩ γ.carrier).Nonempty →
          γ.carrier ∩ K = ({a} : Set (EuclideanSpace ℝ (Fin 2))) →
            ∃ ε : ℝ,
              0 < ε ∧
                (∀ x, x ∈ α.carrier ∩ γ.carrier → ε ≤ dist x a) ∧
                  IsCompact (γ.carrier ∩ {x | ε ≤ dist x a}) ∧
                    Disjoint (γ.carrier ∩ {x | ε ≤ dist x a}) K := by sorry
