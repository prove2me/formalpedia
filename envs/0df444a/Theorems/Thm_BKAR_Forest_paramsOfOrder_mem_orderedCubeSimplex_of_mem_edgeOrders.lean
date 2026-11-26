-- Prove2me | Theorems.Thm_BKAR_Forest_paramsOfOrder_mem_orderedCubeSimplex_of_mem_edgeOrders
-- name    : BKAR.Forest.paramsOfOrder_mem_orderedCubeSimplex_of_mem_edgeOrders
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:30:56.891856+00:00
-- url     : https://prove2.me/theorems/7b44e1df-6c95-5e5f-9b5d-ac4396d450d4
-- title:
--   Forest: params Of Order mem ordered Cube Simplex of mem edge Orders
-- statement:
--   Set-level simplex-sector bridge: ordered-simplex coordinates, sent into cube
--   coordinates
--   by `paramsOfOrder`, land in the ordered cube sector for the same canonical
--   edge order.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/CubeIntegral.lean#L155-L164
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/CubeIntegral.lean#L155-L164

import Mathlib.Data.List.Sort
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Definitions.Def_BKAR_CubePartition_Orders
import Definitions.Def_BKAR_CubePartition_CubeIntegral
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.paramsOfOrder_mem_orderedCubeSimplex_of_mem_edgeOrders
    (F : Forest V) {order : List (Edge V)} (horder : order ∈ F.edgeOrders)
    {ts : List ℝ} (hts : OrderedSimplexParams 1 ts)
    (hlen : ts.length = order.length) :
    F.paramsOfOrder order ts ∈ F.orderedCubeSimplex order := by sorry
