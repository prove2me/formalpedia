-- Prove2me | Theorems.Thm_BKAR_Forest_grownForestForSupportOrder_branchPoint_eq_standardInterp_paramsOfOrder
-- name    : BKAR.Forest.grownForestForSupportOrder_branchPoint_eq_standardInterp_paramsOfOrder
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:03:40.053494+00:00
-- url     : https://prove2.me/theorems/ecf5025e-7953-4aa0-a2fa-f09d6dab3a66
-- title:
--   Forest: grown Forest For Support Order branch Point eq standard Interp params Of Order
-- statement:
--   The branch point attached to a grown support/order forest is exactly its
--   standard interpolation in the same ordered-sector coordinates.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/ChosenGrowth.lean#L118-L130
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/ChosenGrowth.lean#L118-L130

import Definitions.Def_BKAR_OrderedAssembly_CanonicalForestBridge
import Definitions.Def_BKAR_OrderedAssembly_ChosenGrowth
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.grownForestForSupportOrder_branchPoint_eq_standardInterp_paramsOfOrder
    (choices : ActiveExtensionChoice V)
    (I : ForestIndex V)
    (order : {order : List (Edge V) // order ∈ edgeSetOrders I.edges})
    (ts : List ℝ) (hlen : ts.length = order.val.length) :
    (grownForestForSupportOrder_orderedGrowth choices I order).branchPoint
        emptyParam ts =
      (grownForestForSupportOrder choices I order).standardInterp
        ((grownForestForSupportOrder choices I order).paramsOfOrder
          order.val ts) := by sorry
