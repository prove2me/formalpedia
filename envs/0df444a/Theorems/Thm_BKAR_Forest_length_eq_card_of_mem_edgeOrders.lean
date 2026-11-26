-- Prove2me | Theorems.Thm_BKAR_Forest_length_eq_card_of_mem_edgeOrders
-- name    : BKAR.Forest.length_eq_card_of_mem_edgeOrders
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:26:29.097158+00:00
-- url     : https://prove2.me/theorems/c3b30529-76fb-54a7-ad3b-bcd3b0b692e9
-- title:
--   Forest: length eq card of mem edge Orders
-- statement:
--   The Forest construction uses the length eq card of mem edge Orders property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Orders.lean#L385-L388
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Orders.lean#L385-L388

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

theorem BKAR.Forest.length_eq_card_of_mem_edgeOrders (F : Forest V)
    {order : List (Edge V)} (h : order ∈ F.edgeOrders) :
    order.length = F.edges.card := by sorry
