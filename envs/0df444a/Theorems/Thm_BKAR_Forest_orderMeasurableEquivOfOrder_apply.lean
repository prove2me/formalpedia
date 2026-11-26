-- Prove2me | Theorems.Thm_BKAR_Forest_orderMeasurableEquivOfOrder_apply
-- name    : BKAR.Forest.orderMeasurableEquivOfOrder_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:55:30.098801+00:00
-- url     : https://prove2.me/theorems/ab82f8c3-4042-44d9-ac47-f2c662c64c1e
-- title:
--   Forest: order Measurable Equiv Of Order apply
-- statement:
--   The ordered coordinate equivalence reads back the parameter of `order.get i`.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Equiv.lean#L107-L125
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Equiv.lean#L107-L125

import Definitions.Def_BKAR_CubePartition_SimplexSector_Singleton
import Definitions.Def_BKAR_CubePartition_SimplexSector_Equiv
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.orderMeasurableEquivOfOrder_apply
    (F : Forest V) {order : List (Edge V)} (horder : order ∈ F.edgeOrders)
    (u : F.EdgeParam → ℝ) (i : Fin order.length) :
    F.orderMeasurableEquivOfOrder horder u i =
      F.paramValue u (order.get i) := by sorry
