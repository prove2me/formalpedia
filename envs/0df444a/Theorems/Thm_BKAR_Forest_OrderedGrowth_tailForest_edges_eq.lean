-- Prove2me | Theorems.Thm_BKAR_Forest_OrderedGrowth_tailForest_edges_eq
-- name    : BKAR.Forest.OrderedGrowth.tailForest_edges_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:29:43.964468+00:00
-- url     : https://prove2.me/theorems/0e5b7469-b578-4d5e-b4e1-a5f643c1abee
-- title:
--   Ordered Growth: tail Forest edges eq
-- statement:
--   The Ordered Growth construction uses the tail Forest edges eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedForest.lean#L74-L76
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedForest.lean#L74-L76

import Definitions.Def_BKAR_OrderedExpansion
import Definitions.Def_BKAR_OrderedForest
set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}

theorem BKAR.Forest.OrderedGrowth.tailForest_edges_eq (h : OrderedGrowth F (e :: order) G) :
    h.tailForest.edges = insert e F.edges := by sorry
