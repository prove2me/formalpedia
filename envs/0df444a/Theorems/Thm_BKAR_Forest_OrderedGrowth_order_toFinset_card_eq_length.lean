-- Prove2me | Theorems.Thm_BKAR_Forest_OrderedGrowth_order_toFinset_card_eq_length
-- name    : BKAR.Forest.OrderedGrowth.order_toFinset_card_eq_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:36:15.698372+00:00
-- url     : https://prove2.me/theorems/9c5a4579-19c5-43df-96d6-638d610a48e3
-- title:
--   Ordered Growth: order to Finset card eq length
-- statement:
--   The Ordered Growth construction uses the order to Finset card eq length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedForest.lean#L160-L162
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedForest.lean#L160-L162

import Definitions.Def_BKAR_OrderedExpansion
import Definitions.Def_BKAR_OrderedForest
set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}

theorem BKAR.Forest.OrderedGrowth.order_toFinset_card_eq_length (h : OrderedGrowth F order G) :
    order.toFinset.card = order.length := by sorry
