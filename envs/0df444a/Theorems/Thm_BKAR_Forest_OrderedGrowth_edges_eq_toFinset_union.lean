-- Prove2me | Theorems.Thm_BKAR_Forest_OrderedGrowth_edges_eq_toFinset_union
-- name    : BKAR.Forest.OrderedGrowth.edges_eq_toFinset_union
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:27:19.050794+00:00
-- url     : https://prove2.me/theorems/76b05a7c-1f6f-47b2-a297-9f6d353ffbde
-- title:
--   Ordered Growth: edges eq to Finset union
-- statement:
--   Edge-set bookkeeping for an ordered growth certificate.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedForest.lean#L84-L91
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedForest.lean#L84-L91

import Definitions.Def_BKAR_OrderedExpansion
import Definitions.Def_BKAR_OrderedForest
set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}

theorem BKAR.Forest.OrderedGrowth.edges_eq_toFinset_union (h : OrderedGrowth F order G) :
    G.edges = order.toFinset ∪ F.edges := by sorry
