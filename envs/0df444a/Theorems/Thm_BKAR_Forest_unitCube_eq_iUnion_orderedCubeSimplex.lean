-- Prove2me | Theorems.Thm_BKAR_Forest_unitCube_eq_iUnion_orderedCubeSimplex
-- name    : BKAR.Forest.unitCube_eq_iUnion_orderedCubeSimplex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:50:14.085551+00:00
-- url     : https://prove2.me/theorems/b20365e4-adb3-4949-ba98-9d1e5949081e
-- title:
--   Forest: unit Cube eq i Union ordered Cube Simplex
-- statement:
--   Set-level partition cover: the unit cube is the union of its canonical
--   ordered cube sectors. Pairwise disjointness only holds away from coordinate
--   collision hyperplanes, which is the remaining measure-zero part of the
--   unit-cube partition step.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/CubeIntegral.lean#L259-L265
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/CubeIntegral.lean#L259-L265

import Mathlib.Data.List.Sort
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Definitions.Def_BKAR_CubePartition_Orders
import Definitions.Def_BKAR_CubePartition_CubeIntegral
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.unitCube_eq_iUnion_orderedCubeSimplex (F : Forest V) :
    F.unitCube =
      ⋃ order : {order : List (Edge V) // order ∈ F.edgeOrders},
        F.orderedCubeSimplex order.val := by sorry
