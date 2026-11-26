-- Prove2me | Theorems.Thm_BKAR_Forest_continuous_orderMeasurableEquivOfOrder_symm
-- name    : BKAR.Forest.continuous_orderMeasurableEquivOfOrder_symm
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:08:44.682021+00:00
-- url     : https://prove2.me/theorems/d34b7699-2ecc-4726-b84f-feb951d8567e
-- title:
--   Forest: continuous order Measurable Equiv Of Order symm
-- statement:
--   The inverse ordered-coordinate equivalence is continuous.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Equiv.lean#L144-L159
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Equiv.lean#L144-L159

import Definitions.Def_BKAR_CubePartition_SimplexSector_Singleton
import Definitions.Def_BKAR_CubePartition_SimplexSector_Equiv
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.continuous_orderMeasurableEquivOfOrder_symm
    (F : Forest V) {order : List (Edge V)} (horder : order ∈ F.edgeOrders) :
    Continuous
      (fun ts : Fin order.length → ℝ =>
        (F.orderMeasurableEquivOfOrder horder).symm ts) := by sorry
