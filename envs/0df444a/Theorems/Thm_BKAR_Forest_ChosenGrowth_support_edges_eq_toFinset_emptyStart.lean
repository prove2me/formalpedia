-- Prove2me | Theorems.Thm_BKAR_Forest_ChosenGrowth_support_edges_eq_toFinset_emptyStart
-- name    : BKAR.Forest.ChosenGrowth.support_edges_eq_toFinset_emptyStart
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:25:02.501622+00:00
-- url     : https://prove2.me/theorems/758f4645-7a0a-58f4-ae18-07428670664f
-- title:
--   Chosen Growth: support edges eq to Finset empty Start
-- statement:
--   Root-start edge-set bookkeeping for a chosen growth path.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFiberBridge/FollowOrder.lean#L52-L56
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFiberBridge/FollowOrder.lean#L52-L56

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFibers
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_FollowOrder
import Theorems.Thm_BKAR_Forest_TerminalGrowth_support_edges_eq_toFinset_emptyStart

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ChosenGrowth
variable {choices : ActiveExtensionChoice V}
variable {F G : Forest V} {order : List (Edge V)}

theorem BKAR.Forest.ChosenGrowth.support_edges_eq_toFinset_emptyStart
    (path : ChosenGrowth choices (Forest.empty V) order G) :
    G.support.edges = order.toFinset := by sorry
