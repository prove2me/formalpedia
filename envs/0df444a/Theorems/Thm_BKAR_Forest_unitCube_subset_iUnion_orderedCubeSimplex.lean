-- Prove2me | Theorems.Thm_BKAR_Forest_unitCube_subset_iUnion_orderedCubeSimplex
-- name    : BKAR.Forest.unitCube_subset_iUnion_orderedCubeSimplex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:49:46.189424+00:00
-- url     : https://prove2.me/theorems/1ad36b88-21cd-5bd2-b2f2-c8e143c5b7ff
-- title:
--   Forest: unit Cube subset i Union ordered Cube Simplex
-- statement:
--   The ordered cube sectors cover the unit cube.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/CubeIntegral.lean#L233-L242
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/CubeIntegral.lean#L233-L242

import Mathlib.Data.List.Sort
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Definitions.Def_BKAR_CubePartition_Orders
import Definitions.Def_BKAR_CubePartition_CubeIntegral
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.unitCube_subset_iUnion_orderedCubeSimplex (F : Forest V) :
    F.unitCube ⊆
      ⋃ order : {order : List (Edge V) // order ∈ F.edgeOrders},
        F.orderedCubeSimplex order.val := by sorry
