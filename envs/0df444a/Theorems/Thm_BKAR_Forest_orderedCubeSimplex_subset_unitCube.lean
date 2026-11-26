-- Prove2me | Theorems.Thm_BKAR_Forest_orderedCubeSimplex_subset_unitCube
-- name    : BKAR.Forest.orderedCubeSimplex_subset_unitCube
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:49:06.180583+00:00
-- url     : https://prove2.me/theorems/7dc95888-b3f5-4ca6-9ac5-0a123bd5d5f8
-- title:
--   Forest: ordered Cube Simplex subset unit Cube
-- statement:
--   The Forest construction uses the ordered Cube Simplex subset unit Cube property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/CubeIntegral.lean#L55-L59
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/CubeIntegral.lean#L55-L59

import Mathlib.Data.List.Sort
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Definitions.Def_BKAR_CubePartition_Orders
import Definitions.Def_BKAR_CubePartition_CubeIntegral
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.orderedCubeSimplex_subset_unitCube
    (F : Forest V) (order : List (Edge V)) :
    F.orderedCubeSimplex order ⊆ F.unitCube := by sorry
