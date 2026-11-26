-- Prove2me | Theorems.Thm_BKAR_Forest_OrderedGrowth_tailForest_card_edges_eq
-- name    : BKAR.Forest.OrderedGrowth.tailForest_card_edges_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:35:47.434911+00:00
-- url     : https://prove2.me/theorems/53c386d4-cf80-5ceb-acca-923bee8dea50
-- title:
--   Ordered Growth: tail Forest card edges eq
-- statement:
--   The Ordered Growth construction uses the tail Forest card edges eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedForest.lean#L78-L81
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedForest.lean#L78-L81

import Definitions.Def_BKAR_OrderedExpansion
import Definitions.Def_BKAR_OrderedForest
set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}

theorem BKAR.Forest.OrderedGrowth.tailForest_card_edges_eq (h : OrderedGrowth F (e :: order) G) :
    h.tailForest.edges.card = F.edges.card + 1 := by sorry
