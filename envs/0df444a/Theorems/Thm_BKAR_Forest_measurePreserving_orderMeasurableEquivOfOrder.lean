-- Prove2me | Theorems.Thm_BKAR_Forest_measurePreserving_orderMeasurableEquivOfOrder
-- name    : BKAR.Forest.measurePreserving_orderMeasurableEquivOfOrder
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:56:59.796587+00:00
-- url     : https://prove2.me/theorems/14840650-ee95-4567-b585-7795dbab70a2
-- title:
--   Forest: measure Preserving order Measurable Equiv Of Order
-- statement:
--   The Forest construction uses the measure Preserving order Measurable Equiv Of Order property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Equiv.lean#L75-L88
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Equiv.lean#L75-L88

import Definitions.Def_BKAR_CubePartition_SimplexSector_Singleton
import Definitions.Def_BKAR_CubePartition_SimplexSector_Equiv
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.measurePreserving_orderMeasurableEquivOfOrder
    (F : Forest V) {order : List (Edge V)} (horder : order ∈ F.edgeOrders) :
    MeasurePreserving (F.orderMeasurableEquivOfOrder horder)
      (volume : Measure (F.EdgeParam → ℝ))
      (volume : Measure (Fin order.length → ℝ)) := by sorry
