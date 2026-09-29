-- Prove2me | Theorems.Thm_EveryFaceIncidentDart
-- name    : EveryFaceIncidentDart
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-26T21:56:26.880648+00:00
-- url     : https://prove2.me/theorems/ea67f535-630e-4725-ae65-5e485531c3dd
-- title:
--   Every plane face is incident with a dart
-- statement:
--   Let $G$ be a connected finite simple graph with at least three vertices and at least one edge, and let $D$ be a crossing-free ordinary polygonal drawing with plane face data $A$. Then every face $F$ of $A$ is the left face of some dart: there exists a dart $d$ with $A.leftFace\,d=F$.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/EveryFaceIncidentDart.lean#L1-L24

import Definitions.Def_PlaneFaceData
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

open Classical
noncomputable section

lemma EveryFaceIncidentDart {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] [DecidableRel G.Adj] (D : OrdinaryPolygonalDrawing G)
    (hD : D.crossingSet.card = 0) (A : PlaneFaceData G D) :
    G.Connected → 3 ≤ Fintype.card V → 0 < G.edgeFinset.card →
      ∀ F : A.Face, ∃ d : G.Dart, A.leftFace d = F := by sorry
