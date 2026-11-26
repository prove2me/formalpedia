-- Prove2me | Theorems.Thm_BKAR_Forest_paramsOfOrder_mem_unitCube_of_orderedSimplexParams
-- name    : BKAR.Forest.paramsOfOrder_mem_unitCube_of_orderedSimplexParams
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:49:05.933244+00:00
-- url     : https://prove2.me/theorems/a740fbe0-b74a-547e-8751-b8e7c631cc2d
-- title:
--   Forest: params Of Order mem unit Cube of ordered Simplex Params
-- statement:
--   Any ordered-simplex coordinate list gives a point of the unit cube through
--   `paramsOfOrder`. Coordinates not represented in the list use the default `0`.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/CubeIntegral.lean#L70-L85
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/CubeIntegral.lean#L70-L85

import Mathlib.Data.List.Sort
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Definitions.Def_BKAR_CubePartition_Orders
import Definitions.Def_BKAR_CubePartition_CubeIntegral
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.paramsOfOrder_mem_unitCube_of_orderedSimplexParams
    (F : Forest V) (order : List (Edge V)) {ts : List ℝ}
    (hts : OrderedSimplexParams 1 ts) :
    F.paramsOfOrder order ts ∈ F.unitCube := by sorry
