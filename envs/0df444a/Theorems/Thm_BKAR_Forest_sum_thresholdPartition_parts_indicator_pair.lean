-- Prove2me | Theorems.Thm_BKAR_Forest_sum_thresholdPartition_parts_indicator_pair
-- name    : BKAR.Forest.sum_thresholdPartition_parts_indicator_pair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:09:34.86402+00:00
-- url     : https://prove2.me/theorems/5ad5404f-93bd-4c2b-b9ff-f9f20c415b73
-- title:
--   Forest: sum threshold Partition parts indicator pair
-- statement:
--   At a fixed threshold, summing over threshold partition cells gives the
--   component indicator of the threshold component containing `z`.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/ThresholdComponents.lean#L204-L211
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/ThresholdComponents.lean#L204-L211

import Mathlib.Order.Partition.Finpartition
import Definitions.Def_BKAR_ForestGraph
import Definitions.Def_BKAR_Threshold
import Definitions.Def_BKAR_ThresholdComponents
set_option autoImplicit false
open BKAR
open scoped BigOperators
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable section

theorem BKAR.Forest.sum_thresholdPartition_parts_indicator_pair
    (F : Forest V) (u : F.EdgeParam → ℝ) (s r : ℝ) (z w : V) :
    (∑ c : {c : Finset V // c ∈ (F.thresholdPartition u s).parts},
        if z ∈ c.1 ∧ w ∈ c.1 then r else 0) =
      if w ∈ F.thresholdComponent u s z then r else 0 := by sorry
