-- Prove2me | Theorems.Thm_BKAR_Forest_orderMeasurableEquivOfOrder_apply_edgeParam
-- name    : BKAR.Forest.orderMeasurableEquivOfOrder_apply_edgeParam
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:08:07.423458+00:00
-- url     : https://prove2.me/theorems/01c4dd6e-da37-5eea-b82e-22c65a312a62
-- title:
--   Forest: order Measurable Equiv Of Order apply edge Param
-- statement:
--   The ordered coordinate equivalence is, definitionally, readback along the order equivalence.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Equiv.lean#L91-L104
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Equiv.lean#L91-L104

import Definitions.Def_BKAR_CubePartition_SimplexSector_Singleton
import Definitions.Def_BKAR_CubePartition_SimplexSector_Equiv
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.orderMeasurableEquivOfOrder_apply_edgeParam
    (F : Forest V) {order : List (Edge V)} (horder : order ∈ F.edgeOrders)
    (u : F.EdgeParam → ℝ) (i : Fin order.length) :
    F.orderMeasurableEquivOfOrder horder u i =
      u (F.edgeParamFinEquivOfOrder horder i) := by sorry
