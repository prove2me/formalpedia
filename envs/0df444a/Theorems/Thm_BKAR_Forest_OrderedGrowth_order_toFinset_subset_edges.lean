-- Prove2me | Theorems.Thm_BKAR_Forest_OrderedGrowth_order_toFinset_subset_edges
-- name    : BKAR.Forest.OrderedGrowth.order_toFinset_subset_edges
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:29:53.764865+00:00
-- url     : https://prove2.me/theorems/7c2f54a9-5c17-4716-9abb-fc220e309602
-- title:
--   Ordered Growth: order to Finset subset edges
-- statement:
--   The Ordered Growth construction uses the order to Finset subset edges property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedForest.lean#L110-L114
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedForest.lean#L110-L114

import Definitions.Def_BKAR_OrderedExpansion
import Definitions.Def_BKAR_OrderedForest
set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}

theorem BKAR.Forest.OrderedGrowth.order_toFinset_subset_edges (h : OrderedGrowth F order G) :
    order.toFinset ⊆ G.edges := by sorry
