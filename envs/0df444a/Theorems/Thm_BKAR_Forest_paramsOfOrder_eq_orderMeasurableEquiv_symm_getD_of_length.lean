-- Prove2me | Theorems.Thm_BKAR_Forest_paramsOfOrder_eq_orderMeasurableEquiv_symm_getD_of_length
-- name    : BKAR.Forest.paramsOfOrder_eq_orderMeasurableEquiv_symm_getD_of_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:13:26.688322+00:00
-- url     : https://prove2.me/theorems/3344589d-23d5-44b3-bce5-286a2a3f49a4
-- title:
--   Forest: params Of Order eq order Measurable Equiv symm get D of length
-- statement:
--   For parameter lists of the correct length, `paramsOfOrder` is exactly the
--   inverse ordered-coordinate map applied to the corresponding `Fin` tuple.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Finite.lean#L517-L531
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Finite.lean#L517-L531

import Definitions.Def_BKAR_CubePartition_SimplexSector
import Definitions.Def_BKAR_CubePartition_SimplexSector_Finite
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.paramsOfOrder_eq_orderMeasurableEquiv_symm_getD_of_length
    (F : Forest V) {order : List (Edge V)} (horder : order ∈ F.edgeOrders)
    (ts : List ℝ) (hlen : ts.length = order.length) :
    F.paramsOfOrder order ts =
      (F.orderMeasurableEquivOfOrder horder).symm
        (fun i : Fin order.length => ts.getD i.val 0) := by sorry
