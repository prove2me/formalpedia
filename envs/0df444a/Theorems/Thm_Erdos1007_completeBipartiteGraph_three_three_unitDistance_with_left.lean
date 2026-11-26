-- Prove2me | Theorems.Thm_Erdos1007_completeBipartiteGraph_three_three_unitDistance_with_left
-- name    : Erdos1007.completeBipartiteGraph_three_three_unitDistance_with_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:53:18.920875+00:00
-- url     : https://prove2.me/theorems/46b505c6-18ab-451c-80d5-1e41cac1445d
-- title:
--   Erdos1007: complete Bipartite Graph three three unit Distance with left
-- statement:
--   The placement of `K₃,₃` in `ℝ⁴` realises every cross edge, and also the segment joining
--   `(r, 0, 0, 0)` to `(0, r, 0, 0)`, as a unit segment.
--
--   Source: https://github.com/Dishah3241/Erdos1007/blob/43f89415a6663848a1445effbda8b3abe77b052b/Erdos1007/Geometry/CompleteBipartite.lean#L56-L120
-- source:
--   https://github.com/Dishah3241/Erdos1007/blob/43f89415a6663848a1445effbda8b3abe77b052b/Erdos1007/Geometry/CompleteBipartite.lean#L56-L120

module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Definitions.Def_Erdos1007_Geometry_CompleteBipartite
set_option autoImplicit false
@[expose] public section
open Erdos1007
public section

theorem Erdos1007.completeBipartiteGraph_three_three_unitDistance_with_left :
    ∃ f : Fin 3 ⊕ Fin 3 → EuclideanSpace ℝ (Fin 4), Function.Injective f ∧
      (∀ u v, (completeBipartiteGraph (Fin 3) (Fin 3)).Adj u v → dist (f u) (f v) = 1) ∧
      dist (f (Sum.inl 0)) (f (Sum.inl 2)) = 1 := by sorry
