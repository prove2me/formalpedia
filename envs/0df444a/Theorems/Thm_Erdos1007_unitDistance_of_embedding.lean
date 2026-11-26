-- Prove2me | Theorems.Thm_Erdos1007_unitDistance_of_embedding
-- name    : Erdos1007.unitDistance_of_embedding
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:53:04.521475+00:00
-- url     : https://prove2.me/theorems/b3b90237-4f14-5bd0-9a74-4d2a406db068
-- title:
--   Erdos1007: unit Distance of embedding
-- statement:
--   A unit-distance representation of `G` pulls back along a graph embedding `H ↪g G`
--   (blueprint node `lem:monotone`; Chaffee–Noble Lemma 4).
--
--   Source: https://github.com/Dishah3241/Erdos1007/blob/43f89415a6663848a1445effbda8b3abe77b052b/Erdos1007/Geometry/UnitDistanceComap.lean#L64-L70
-- source:
--   https://github.com/Dishah3241/Erdos1007/blob/43f89415a6663848a1445effbda8b3abe77b052b/Erdos1007/Geometry/UnitDistanceComap.lean#L64-L70

module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Definitions.Def_Erdos1007_Geometry_UnitDistanceComap
set_option autoImplicit false
@[expose] public section
open Erdos1007
open SimpleGraph
public section

theorem Erdos1007.unitDistance_of_embedding {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} {n : ℕ}
    (φ : H ↪g G) :
    (∃ f : V → EuclideanSpace ℝ (Fin n), Function.Injective f ∧
        ∀ u v, G.Adj u v → dist (f u) (f v) = 1) →
      ∃ g : W → EuclideanSpace ℝ (Fin n), Function.Injective g ∧
        ∀ u v, H.Adj u v → dist (g u) (g v) = 1 := by sorry
