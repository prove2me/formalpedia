-- Prove2me | Theorems.Thm_BKAR_Forest_boundarySupportOrderTreeFiber_eq_zero_of_order_toFinset_ne_edges
-- name    : BKAR.Forest.boundarySupportOrderTreeFiber_eq_zero_of_order_toFinset_ne_edges
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:18:53.175316+00:00
-- url     : https://prove2.me/theorems/7dd99cee-88db-47f9-8e7c-211af924b493
-- title:
--   Forest: boundary Support Order Tree Fiber eq zero of order to Finset ne edges
-- statement:
--   A support/order fiber can contribute only when the requested order has exactly
--   the requested support edge set.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFiberBridge/Core.lean#L64-L127
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFiberBridge/Core.lean#L64-L127

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_FollowOrder
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_Core
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.boundarySupportOrderTreeFiber_eq_zero_of_order_toFinset_ne_edges
    (choices : ActiveExtensionChoice V) :
    ∀ (n : Nat) (F : Forest V) (pref : List (Edge V))
      (prefixTs : List ℝ) (top : ℝ) (I : ForestIndex V)
      (order : List (Edge V)) (ρ : (Edge V → ℝ) → ℝ),
      F.activeEdges.card ≤ n →
      pref.toFinset = F.edges →
      order.toFinset ≠ I.edges →
      boundarySupportOrderTreeFiber choices F pref prefixTs top
        I order ρ = 0
  := by sorry
