-- Prove2me | Theorems.Thm_BKAR_Forest_map_paramValue_paramsOfOrder_eq_of_mem_edgeOrders
-- name    : BKAR.Forest.map_paramValue_paramsOfOrder_eq_of_mem_edgeOrders
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:49:16.493862+00:00
-- url     : https://prove2.me/theorems/9ada42de-7706-5ed9-a91f-ef5d7d0b7e57
-- title:
--   Forest: map param Value params Of Order eq of mem edge Orders
-- statement:
--   For a canonical edge order, `paramsOfOrder` is a right inverse to the sector
--   coordinate readback map.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/CubeIntegral.lean#L135-L147
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/CubeIntegral.lean#L135-L147

import Mathlib.Data.List.Sort
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Definitions.Def_BKAR_CubePartition_Orders
import Definitions.Def_BKAR_CubePartition_CubeIntegral
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.map_paramValue_paramsOfOrder_eq_of_mem_edgeOrders
    (F : Forest V) {order : List (Edge V)} (horder : order ∈ F.edgeOrders)
    {ts : List ℝ} (hlen : ts.length = order.length) :
    order.map (F.paramValue (F.paramsOfOrder order ts)) = ts := by sorry
