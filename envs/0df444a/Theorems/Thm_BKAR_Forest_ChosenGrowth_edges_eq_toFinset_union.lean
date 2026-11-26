-- Prove2me | Theorems.Thm_BKAR_Forest_ChosenGrowth_edges_eq_toFinset_union
-- name    : BKAR.Forest.ChosenGrowth.edges_eq_toFinset_union
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:18:14.817363+00:00
-- url     : https://prove2.me/theorems/54ddac48-993f-5d5a-9ccc-1bf6a5b06868
-- title:
--   Chosen Growth: edges eq to Finset union
-- statement:
--   Edge-set bookkeeping for a chosen growth path.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFiberBridge/FollowOrder.lean#L39-L49
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFiberBridge/FollowOrder.lean#L39-L49

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFibers
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_FollowOrder
import Theorems.Thm_BKAR_Forest_OrderedGrowth_edges_eq_toFinset_union
import Theorems.Thm_BKAR_Forest_TerminalGrowth_edges_eq_toFinset_union

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ChosenGrowth
variable {choices : ActiveExtensionChoice V}
variable {F G : Forest V} {order : List (Edge V)}

theorem BKAR.Forest.ChosenGrowth.edges_eq_toFinset_union
    (path : ChosenGrowth choices F order G) :
    G.edges = order.toFinset ∪ F.edges := by sorry
