-- Prove2me | Theorems.Thm_BKAR_Forest_boundarySupportOrderTreeFiber_eq_localBoundary_of_order_length_eq_succ
-- name    : BKAR.Forest.boundarySupportOrderTreeFiber_eq_localBoundary_of_order_length_eq_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:07:07.621583+00:00
-- url     : https://prove2.me/theorems/ec71c0c5-ca17-5b50-8a24-0e5e25c01013
-- title:
--   Forest: boundary Support Order Tree Fiber eq local Boundary of order length eq succ
-- statement:
--   At a node whose requested global order is exactly one edge longer than the
--   current prefix, the recursive fiber has no child remainder: every child has
--   already consumed the whole requested order.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFiberBridge/Core.lean#L25-L58
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFiberBridge/Core.lean#L25-L58

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_FollowOrder
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_Core
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.boundarySupportOrderTreeFiber_eq_localBoundary_of_order_length_eq_succ
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (I : ForestIndex V) (order : List (Edge V))
    (ρ : (Edge V → ℝ) → ℝ)
    (hlen : order.length = pref.length + 1) :
    boundarySupportOrderTreeFiber choices F pref prefixTs top I order ρ =
      localBoundarySupportOrderContribution choices F pref prefixTs top
        I order ρ := by sorry
