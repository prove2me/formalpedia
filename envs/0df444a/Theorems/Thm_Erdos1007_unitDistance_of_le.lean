-- Prove2me | Theorems.Thm_Erdos1007_unitDistance_of_le
-- name    : Erdos1007.unitDistance_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:53:23.574547+00:00
-- url     : https://prove2.me/theorems/1833785e-db62-4067-b36c-e18fd50966a8
-- title:
--   Erdos1007: unit Distance of le
-- statement:
--   A unit-distance representation of `G` restricts to any spanning subgraph `H ≤ G` on the same
--   vertex type (blueprint node `lem:monotone`; Chaffee–Noble Lemma 4).
--
--   Source: https://github.com/Dishah3241/Erdos1007/blob/43f89415a6663848a1445effbda8b3abe77b052b/Erdos1007/Geometry/UnitDistanceComap.lean#L55-L60
-- source:
--   https://github.com/Dishah3241/Erdos1007/blob/43f89415a6663848a1445effbda8b3abe77b052b/Erdos1007/Geometry/UnitDistanceComap.lean#L55-L60

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

theorem Erdos1007.unitDistance_of_le {V : Type*} {G H : SimpleGraph V} {n : ℕ} (hHG : H ≤ G) :
    (∃ f : V → EuclideanSpace ℝ (Fin n), Function.Injective f ∧
        ∀ u v, G.Adj u v → dist (f u) (f v) = 1) →
      ∃ g : V → EuclideanSpace ℝ (Fin n), Function.Injective g ∧
        ∀ u v, H.Adj u v → dist (g u) (g v) = 1 := by sorry
