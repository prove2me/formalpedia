-- Prove2me | Theorems.Thm_BKAR_Forest_OrderedGrowth_card_edges_eq
-- name    : BKAR.Forest.OrderedGrowth.card_edges_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:30:10.727328+00:00
-- url     : https://prove2.me/theorems/c5747bf7-e1bb-46d3-976e-0e984d64d5f4
-- title:
--   Ordered Growth: card edges eq
-- statement:
--   The final forest has exactly `order.length` more edges than the start.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedForest.lean#L165-L173
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedForest.lean#L165-L173

import Definitions.Def_BKAR_OrderedExpansion
import Definitions.Def_BKAR_OrderedForest
set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}

theorem BKAR.Forest.OrderedGrowth.card_edges_eq (h : OrderedGrowth F order G) :
    G.edges.card = F.edges.card + order.length := by sorry
