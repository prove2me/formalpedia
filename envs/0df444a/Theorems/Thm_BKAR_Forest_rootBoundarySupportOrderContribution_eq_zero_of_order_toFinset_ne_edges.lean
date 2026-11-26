-- Prove2me | Theorems.Thm_BKAR_Forest_rootBoundarySupportOrderContribution_eq_zero_of_order_toFinset_ne_edges
-- name    : BKAR.Forest.rootBoundarySupportOrderContribution_eq_zero_of_order_toFinset_ne_edges
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:07:24.564529+00:00
-- url     : https://prove2.me/theorems/d78f1171-2f45-4c24-b760-5ba957c70cb3
-- title:
--   Forest: root Boundary Support Order Contribution eq zero of order to Finset ne edges
-- statement:
--   Root fibers vanish unless the requested order has the requested support.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFiberBridge/Core.lean#L199-L214
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFiberBridge/Core.lean#L199-L214

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_FollowOrder
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_Core
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.rootBoundarySupportOrderContribution_eq_zero_of_order_toFinset_ne_edges
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ)
    (I : ForestIndex V) (order : List (Edge V))
    (hI : order.toFinset ≠ I.edges) :
    rootBoundarySupportOrderContribution choices ρ I order = 0 := by sorry
