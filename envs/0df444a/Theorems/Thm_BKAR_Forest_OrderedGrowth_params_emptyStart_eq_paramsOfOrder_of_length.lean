-- Prove2me | Theorems.Thm_BKAR_Forest_OrderedGrowth_params_emptyStart_eq_paramsOfOrder_of_length
-- name    : BKAR.Forest.OrderedGrowth.params_emptyStart_eq_paramsOfOrder_of_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:48:31.355791+00:00
-- url     : https://prove2.me/theorems/1b62aebf-44ae-477b-894f-7dac62318176
-- title:
--   Ordered Growth: params empty Start eq params Of Order of length
-- statement:
--   For an ordered growth from the empty forest, the recursive branch parameters
--   are exactly the canonical parameters attached to its terminal edge order.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Orders.lean#L598-L605
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Orders.lean#L598-L605

import Mathlib.Data.List.GetD
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.List.Permutation
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Definitions.Def_BKAR_CubePartition_Orders
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {order : List (Edge V)}

theorem BKAR.Forest.OrderedGrowth.params_emptyStart_eq_paramsOfOrder_of_length
    (h : OrderedGrowth (Forest.empty V) order G)
    {ts : List ℝ} (hlen : ts.length = order.length) :
    h.params emptyParam ts = G.paramsOfOrder order ts := by sorry
