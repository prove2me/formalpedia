-- Prove2me | Theorems.Thm_BKAR_Forest_rootBoundarySupportOrderContribution_eq_grownForestForSupportOrder
-- name    : BKAR.Forest.rootBoundarySupportOrderContribution_eq_grownForestForSupportOrder
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:56:02.494753+00:00
-- url     : https://prove2.me/theorems/296798fc-2c74-45d5-98f6-8f1312ce2899
-- title:
--   Forest: root Boundary Support Order Contribution eq grown Forest For Support Order
-- statement:
--   Canonical-representative bridge for one support/order sector: the root support fiber is
--   the ordered contribution of the `Forest` representative grown by following that order.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/CanonicalForestBridge.lean#L137-L173
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/CanonicalForestBridge.lean#L137-L173

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge
import Definitions.Def_BKAR_OrderedAssembly_CanonicalForestBridge
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.rootBoundarySupportOrderContribution_eq_grownForestForSupportOrder
    (choices : ActiveExtensionChoice V)
    (I : ForestIndex V)
    (order : {order : List (Edge V) // order ∈ edgeSetOrders I.edges})
    (ρ : (Edge V → ℝ) → ℝ) :
    rootBoundarySupportOrderContribution choices ρ I order.val =
      (grownForestForSupportOrder choices I order).orderedContribution
        order.val ρ := by sorry
