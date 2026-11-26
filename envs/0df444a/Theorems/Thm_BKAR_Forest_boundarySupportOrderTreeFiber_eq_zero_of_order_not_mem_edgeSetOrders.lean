-- Prove2me | Theorems.Thm_BKAR_Forest_boundarySupportOrderTreeFiber_eq_zero_of_order_not_mem_edgeSetOrders
-- name    : BKAR.Forest.boundarySupportOrderTreeFiber_eq_zero_of_order_not_mem_edgeSetOrders
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:18:33.130834+00:00
-- url     : https://prove2.me/theorems/7fd873b7-fdd8-5acc-b1b6-ddd89a371945
-- title:
--   Forest: boundary Support Order Tree Fiber eq zero of order not mem edge Set Orders
-- statement:
--   A support/order fiber can contribute only for canonical orders of the requested
--   support.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFiberBridge/Core.lean#L220-L295
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFiberBridge/Core.lean#L220-L295

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_FollowOrder
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_Core
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.boundarySupportOrderTreeFiber_eq_zero_of_order_not_mem_edgeSetOrders
    (choices : ActiveExtensionChoice V) :
    ∀ (n : Nat) (F : Forest V) (pref : List (Edge V))
      (prefixTs : List ℝ) (top : ℝ) (I : ForestIndex V)
      (order : List (Edge V)) (ρ : (Edge V → ℝ) → ℝ),
      F.activeEdges.card ≤ n →
      pref.toFinset = F.edges →
      pref.Nodup →
      order ∉ edgeSetOrders I.edges →
      boundarySupportOrderTreeFiber choices F pref prefixTs top
        I order ρ = 0
  := by sorry
