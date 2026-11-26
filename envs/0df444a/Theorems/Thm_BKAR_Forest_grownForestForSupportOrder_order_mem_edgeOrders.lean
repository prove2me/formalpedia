-- Prove2me | Theorems.Thm_BKAR_Forest_grownForestForSupportOrder_order_mem_edgeOrders
-- name    : BKAR.Forest.grownForestForSupportOrder_order_mem_edgeOrders
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:54:58.389469+00:00
-- url     : https://prove2.me/theorems/f70d17b5-0e56-43ce-bc8c-8952d266e91b
-- title:
--   Forest: grown Forest For Support Order order mem edge Orders
-- statement:
--   The Forest construction uses the grown Forest For Support Order order mem edge Orders property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/CanonicalForestBridge.lean#L83-L92
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/CanonicalForestBridge.lean#L83-L92

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge
import Definitions.Def_BKAR_OrderedAssembly_CanonicalForestBridge
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.grownForestForSupportOrder_order_mem_edgeOrders
    (choices : ActiveExtensionChoice V)
    (I : ForestIndex V)
    (order : {order : List (Edge V) // order ∈ edgeSetOrders I.edges}) :
    order.val ∈ (grownForestForSupportOrder choices I order).edgeOrders := by sorry
