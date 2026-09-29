-- Prove2me | Theorems.Thm_ConnectedEulerFormula
-- name    : ConnectedEulerFormula
-- status  : Open
-- author  : @xuanji
-- created : 2026-09-26T21:36:03.819302+00:00
-- url     : https://prove2.me/theorems/779c148f-4cf4-454e-bbfe-e72941cfe9f1
-- title:
--   Euler formula for connected plane drawings
-- statement:
--   For a connected finite graph with a crossing-free ordinary polygonal drawing, the numbers of vertices, edges, and indexed faces satisfy the Euler relation n minus e plus f equals 2.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/ConnectedEulerFormula.lean#L1-L93

import Definitions.Def_PlaneFaceData
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

open Classical
noncomputable section

lemma ConnectedEulerFormula {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] [DecidableRel G.Adj] (D : OrdinaryPolygonalDrawing G)
    (hD : D.crossingSet.card = 0) (A : PlaneFaceData G D) :
    G.Connected →
      (Fintype.card V : ℤ) - (G.edgeFinset.card : ℤ) +
        (@Fintype.card A.Face A.faceFintype : ℤ) = 2 := by sorry
