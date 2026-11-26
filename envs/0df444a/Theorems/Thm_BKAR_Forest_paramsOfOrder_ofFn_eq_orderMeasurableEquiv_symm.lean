-- Prove2me | Theorems.Thm_BKAR_Forest_paramsOfOrder_ofFn_eq_orderMeasurableEquiv_symm
-- name    : BKAR.Forest.paramsOfOrder_ofFn_eq_orderMeasurableEquiv_symm
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:09:12.527929+00:00
-- url     : https://prove2.me/theorems/6b8037d7-b59e-45d2-9d6f-d61c2a2407ae
-- title:
--   Forest: params Of Order of Fn eq order Measurable Equiv symm
-- statement:
--   The inverse coordinate equivalence is the same point of the forest cube as
--   `paramsOfOrder`, when the coordinate list is formed from the `Fin` tuple.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Equiv.lean#L165-L194
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Equiv.lean#L165-L194

import Definitions.Def_BKAR_CubePartition_SimplexSector_Singleton
import Definitions.Def_BKAR_CubePartition_SimplexSector_Equiv
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.paramsOfOrder_ofFn_eq_orderMeasurableEquiv_symm
    (F : Forest V) {order : List (Edge V)} (horder : order ∈ F.edgeOrders)
    (ts : Fin order.length → ℝ) :
    F.paramsOfOrder order (List.ofFn ts) =
      (F.orderMeasurableEquivOfOrder horder).symm ts := by sorry
