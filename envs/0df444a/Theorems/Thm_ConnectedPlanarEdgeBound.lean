-- Prove2me | Theorems.Thm_ConnectedPlanarEdgeBound
-- name    : ConnectedPlanarEdgeBound
-- status  : Open
-- author  : @xuanji
-- created : 2026-09-26T21:20:38.268985+00:00
-- url     : https://prove2.me/theorems/665b76e7-3777-4480-a8f9-a888f92bb95b
-- title:
--   Edge bound for a connected crossing-free ordinary drawing
-- statement:
--   Let $G$ be a finite connected simple graph with at least three vertices. If $G$ admits an ordinary polygonal drawing whose crossing set has cardinality zero, then its number of edges is at most
--
--   $$
--   |E(G)|\le 3|V(G)|-6.
--   $$
--
--   This is the connected planar edge bound used in the global estimate; it is the Euler-formula argument for a crossing-free ordinary drawing.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/ConnectedPlanarEdgeBound.lean#L1-L44

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Definitions.Def_OrdinaryPolygonalDrawing

open Classical
noncomputable section

lemma ConnectedPlanarEdgeBound {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] :
    G.Connected → 3 ≤ Fintype.card V →
      (∃ D : OrdinaryPolygonalDrawing G, D.crossingSet.card = 0) →
        G.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by sorry
