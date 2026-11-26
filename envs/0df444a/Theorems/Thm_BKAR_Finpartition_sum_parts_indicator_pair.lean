-- Prove2me | Theorems.Thm_BKAR_Finpartition_sum_parts_indicator_pair
-- name    : BKAR.Finpartition.sum_parts_indicator_pair
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:18:11.83025+00:00
-- url     : https://prove2.me/theorems/36361e81-9b50-5671-b96b-e98ccb425de4
-- title:
--   Finpartition: sum parts indicator pair
-- statement:
--   Summing the indicator of “`z` and `w` lie in the same part” over the parts of a
--   finite partition leaves exactly the indicator of the part containing `z`.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/ThresholdComponents.lean#L30-L59
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/ThresholdComponents.lean#L30-L59

import Mathlib.Order.Partition.Finpartition
import Definitions.Def_BKAR_ForestGraph
import Definitions.Def_BKAR_Threshold
import Definitions.Def_BKAR_ThresholdComponents
set_option autoImplicit false
open BKAR
open scoped BigOperators
open BKAR.Finpartition
variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable section

theorem BKAR.Finpartition.sum_parts_indicator_pair
    (P : Finpartition (Finset.univ : Finset V)) (r : ℝ) (z w : V) :
    (∑ c : {c : Finset V // c ∈ P.parts},
        if z ∈ c.1 ∧ w ∈ c.1 then r else 0) =
      if w ∈ P.part z then r else 0 := by sorry
