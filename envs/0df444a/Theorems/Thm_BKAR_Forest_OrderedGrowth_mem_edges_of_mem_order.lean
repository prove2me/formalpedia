-- Prove2me | Theorems.Thm_BKAR_Forest_OrderedGrowth_mem_edges_of_mem_order
-- name    : BKAR.Forest.OrderedGrowth.mem_edges_of_mem_order
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:28:11.789366+00:00
-- url     : https://prove2.me/theorems/4a562d38-da57-5d9a-bbc7-6ff735d85fb5
-- title:
--   Ordered Growth: mem edges of mem order
-- statement:
--   The Ordered Growth construction uses the mem edges of mem order property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedForest.lean#L122-L125
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedForest.lean#L122-L125

import Definitions.Def_BKAR_OrderedExpansion
import Definitions.Def_BKAR_OrderedForest
set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}

theorem BKAR.Forest.OrderedGrowth.mem_edges_of_mem_order (h : OrderedGrowth F order G) {e : Edge V}
    (he : e ∈ order) :
    e ∈ G.edges := by sorry
