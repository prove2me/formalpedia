-- Prove2me | Theorems.Thm_BKAR_Forest_OrderedGrowth_support_edges_eq_toFinset_union
-- name    : BKAR.Forest.OrderedGrowth.support_edges_eq_toFinset_union
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:36:06.36089+00:00
-- url     : https://prove2.me/theorems/255c4b56-2543-5170-9f39-9b64a3d84765
-- title:
--   Ordered Growth: support edges eq to Finset union
-- statement:
--   The Ordered Growth construction uses the support edges eq to Finset union property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedForest.lean#L106-L108
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedForest.lean#L106-L108

import Definitions.Def_BKAR_OrderedExpansion
import Definitions.Def_BKAR_OrderedForest
set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}

theorem BKAR.Forest.OrderedGrowth.support_edges_eq_toFinset_union (h : OrderedGrowth F order G) :
    h.support.edges = order.toFinset ∪ F.edges := by sorry
