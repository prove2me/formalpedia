-- Prove2me | Theorems.Thm_BKAR_Forest_OrderedGrowth_order_toFinset_disjoint_initial_edges
-- name    : BKAR.Forest.OrderedGrowth.order_toFinset_disjoint_initial_edges
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:30:01.439065+00:00
-- url     : https://prove2.me/theorems/eea5ce2c-8eee-4aac-b0a1-dff1973019b3
-- title:
--   Ordered Growth: order to Finset disjoint initial edges
-- statement:
--   The ordered-growth list is disjoint from the starting forest's edge set.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedForest.lean#L128-L142
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedForest.lean#L128-L142

import Definitions.Def_BKAR_OrderedExpansion
import Definitions.Def_BKAR_OrderedForest
set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}

theorem BKAR.Forest.OrderedGrowth.order_toFinset_disjoint_initial_edges (h : OrderedGrowth F order G) :
    Disjoint order.toFinset F.edges := by sorry
