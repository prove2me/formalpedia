-- Prove2me | Theorems.Thm_BKAR_Forest_le_standardInterp_iff_mem_thresholdComponent
-- name    : BKAR.Forest.le_standardInterp_iff_mem_thresholdComponent
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:18:18.261421+00:00
-- url     : https://prove2.me/theorems/c3dcddce-a534-5b98-b918-ba41aaf76b9b
-- title:
--   Forest: le standard Interp iff mem threshold Component
-- statement:
--   Positive-threshold layer-set form of the BKAR interpolation value: the edge
--   value is above `s` exactly when the endpoints lie in the same threshold
--   component.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/ThresholdComponents.lean#L191-L198
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/ThresholdComponents.lean#L191-L198

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

theorem BKAR.Forest.le_standardInterp_iff_mem_thresholdComponent
    (F : Forest V) (u : F.EdgeParam → ℝ)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1)
    (e : Edge V) :
    s ≤ F.standardInterp u e ↔
      e.right ∈ F.thresholdComponent u s e.left := by sorry
