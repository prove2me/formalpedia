-- Prove2me | Theorems.Thm_BKAR_Forest_orderMeasurableEquivOfOrder_symm_apply
-- name    : BKAR.Forest.orderMeasurableEquivOfOrder_symm_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:08:12.248284+00:00
-- url     : https://prove2.me/theorems/fbc52bc2-5ff9-4cac-9d64-7c1ad90b5cab
-- title:
--   Forest: order Measurable Equiv Of Order symm apply
-- statement:
--   The Forest construction uses the order Measurable Equiv Of Order symm apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Equiv.lean#L127-L141
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Equiv.lean#L127-L141

import Definitions.Def_BKAR_CubePartition_SimplexSector_Singleton
import Definitions.Def_BKAR_CubePartition_SimplexSector_Equiv
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.orderMeasurableEquivOfOrder_symm_apply
    (F : Forest V) {order : List (Edge V)} (horder : order ∈ F.edgeOrders)
    (ts : Fin order.length → ℝ) (p : F.EdgeParam) :
    (F.orderMeasurableEquivOfOrder horder).symm ts p =
      ts ((F.edgeParamFinEquivOfOrder horder).symm p) := by sorry
