-- Prove2me | Theorems.Thm_BKAR_Forest_OrderedGrowth_tailGrowth_card_edges_eq
-- name    : BKAR.Forest.OrderedGrowth.tailGrowth_card_edges_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:36:53.115939+00:00
-- url     : https://prove2.me/theorems/9483afee-0516-5fa2-9404-572f24a40a70
-- title:
--   Ordered Growth: tail Growth card edges eq
-- statement:
--   The Ordered Growth construction uses the tail Growth card edges eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedForest.lean#L175-L177
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedForest.lean#L175-L177

import Definitions.Def_BKAR_OrderedExpansion
import Definitions.Def_BKAR_OrderedForest
set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}

theorem BKAR.Forest.OrderedGrowth.tailGrowth_card_edges_eq (h : OrderedGrowth F (e :: order) G) :
    G.edges.card = h.tailForest.edges.card + order.length := by sorry
