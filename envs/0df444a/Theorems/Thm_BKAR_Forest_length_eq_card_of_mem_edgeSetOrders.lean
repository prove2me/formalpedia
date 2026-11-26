-- Prove2me | Theorems.Thm_BKAR_Forest_length_eq_card_of_mem_edgeSetOrders
-- name    : BKAR.Forest.length_eq_card_of_mem_edgeSetOrders
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:46:42.261263+00:00
-- url     : https://prove2.me/theorems/9e5bce44-bef3-416c-919d-2a5670f6b1cd
-- title:
--   Forest: length eq card of mem edge Set Orders
-- statement:
--   The Forest construction uses the length eq card of mem edge Set Orders property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Orders.lean#L80-L87
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Orders.lean#L80-L87

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
omit [Fintype V]

theorem BKAR.Forest.length_eq_card_of_mem_edgeSetOrders
    {S : Finset (Edge V)} {order : List (Edge V)}
    (h : order ∈ edgeSetOrders S) :
    order.length = S.card := by sorry
