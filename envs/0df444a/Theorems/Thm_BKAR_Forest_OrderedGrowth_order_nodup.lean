-- Prove2me | Theorems.Thm_BKAR_Forest_OrderedGrowth_order_nodup
-- name    : BKAR.Forest.OrderedGrowth.order_nodup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:29:48.45578+00:00
-- url     : https://prove2.me/theorems/894bcb75-c005-5868-b123-c11b79db559a
-- title:
--   Ordered Growth: order nodup
-- statement:
--   An ordered-growth list never repeats an edge.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedForest.lean#L145-L158
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedForest.lean#L145-L158

import Definitions.Def_BKAR_OrderedExpansion
import Definitions.Def_BKAR_OrderedForest
set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}

theorem BKAR.Forest.OrderedGrowth.order_nodup (h : OrderedGrowth F order G) :
    order.Nodup := by sorry
