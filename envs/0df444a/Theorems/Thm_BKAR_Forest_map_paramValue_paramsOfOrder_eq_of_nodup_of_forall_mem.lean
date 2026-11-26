-- Prove2me | Theorems.Thm_BKAR_Forest_map_paramValue_paramsOfOrder_eq_of_nodup_of_forall_mem
-- name    : BKAR.Forest.map_paramValue_paramsOfOrder_eq_of_nodup_of_forall_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:49:12.826034+00:00
-- url     : https://prove2.me/theorems/e730d003-6d96-51b7-8ef1-3c5af29f8b51
-- title:
--   Forest: map param Value params Of Order eq of nodup of forall mem
-- statement:
--   Reading back the parameters of a nodup order from `paramsOfOrder` recovers the
--   original coordinate list, provided the list lengths match.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/CubeIntegral.lean#L91-L129
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/CubeIntegral.lean#L91-L129

import Mathlib.Data.List.Sort
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Definitions.Def_BKAR_CubePartition_Orders
import Definitions.Def_BKAR_CubePartition_CubeIntegral
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.map_paramValue_paramsOfOrder_eq_of_nodup_of_forall_mem
    (F : Forest V) :
    ∀ (order : List (Edge V)) {ts : List ℝ},
      order.Nodup →
      (∀ e ∈ order, e ∈ F.edges) →
      ts.length = order.length →
      order.map (F.paramValue (F.paramsOfOrder order ts)) = ts
  := by sorry
