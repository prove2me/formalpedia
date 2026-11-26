-- Prove2me | Theorems.Thm_BKAR_Forest_iUnion_orderedCubeSimplex_subset_unitCube
-- name    : BKAR.Forest.iUnion_orderedCubeSimplex_subset_unitCube
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:49:59.415731+00:00
-- url     : https://prove2.me/theorems/273b97b2-53e4-4707-8871-097859c1b883
-- title:
--   Forest: i Union ordered Cube Simplex subset unit Cube
-- statement:
--   Every ordered cube sector is contained in the unit cube.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/CubeIntegral.lean#L245-L251
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/CubeIntegral.lean#L245-L251

import Mathlib.Data.List.Sort
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Definitions.Def_BKAR_CubePartition_Orders
import Definitions.Def_BKAR_CubePartition_CubeIntegral
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.iUnion_orderedCubeSimplex_subset_unitCube (F : Forest V) :
    (⋃ order : {order : List (Edge V) // order ∈ F.edgeOrders},
        F.orderedCubeSimplex order.val) ⊆ F.unitCube := by sorry
