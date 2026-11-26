-- Prove2me | Theorems.Thm_BKAR_Forest_rootBoundarySupportOrderContribution_eq_zero_of_order_not_mem_edgeSetOrders
-- name    : BKAR.Forest.rootBoundarySupportOrderContribution_eq_zero_of_order_not_mem_edgeSetOrders
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:51:10.582813+00:00
-- url     : https://prove2.me/theorems/e6b11449-3be3-41a6-b8d3-1e9e8221c763
-- title:
--   Forest: root Boundary Support Order Contribution eq zero of order not mem edge Set Orders
-- statement:
--   Root fibers vanish off the canonical order set of the requested support.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFiberBridge/Core.lean#L298-L314
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFiberBridge/Core.lean#L298-L314

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_FollowOrder
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_Core
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.rootBoundarySupportOrderContribution_eq_zero_of_order_not_mem_edgeSetOrders
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ)
    (I : ForestIndex V) (order : List (Edge V))
    (horder : order ∉ edgeSetOrders I.edges) :
    rootBoundarySupportOrderContribution choices ρ I order = 0 := by sorry
