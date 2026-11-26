-- Prove2me | Theorems.Thm_BKAR_Forest_OrderedGrowth_initial_edges_subset_edges
-- name    : BKAR.Forest.OrderedGrowth.initial_edges_subset_edges
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:27:57.481915+00:00
-- url     : https://prove2.me/theorems/697694f9-f6eb-4815-87f4-77426beb77af
-- title:
--   Ordered Growth: initial edges subset edges
-- statement:
--   The Ordered Growth construction uses the initial edges subset edges property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedForest.lean#L116-L120
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedForest.lean#L116-L120

import Definitions.Def_BKAR_OrderedExpansion
import Definitions.Def_BKAR_OrderedForest
set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}

theorem BKAR.Forest.OrderedGrowth.initial_edges_subset_edges (h : OrderedGrowth F order G) :
    F.edges ⊆ G.edges := by sorry
