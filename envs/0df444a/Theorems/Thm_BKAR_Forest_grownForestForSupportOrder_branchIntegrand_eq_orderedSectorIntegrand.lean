-- Prove2me | Theorems.Thm_BKAR_Forest_grownForestForSupportOrder_branchIntegrand_eq_orderedSectorIntegrand
-- name    : BKAR.Forest.grownForestForSupportOrder_branchIntegrand_eq_orderedSectorIntegrand
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:03:37.201676+00:00
-- url     : https://prove2.me/theorems/a9784c40-45c4-4c20-ab52-88c0d8805023
-- title:
--   Forest: grown Forest For Support Order branch Integrand eq ordered Sector Integrand
-- statement:
--   The grown support/order branch integrand is the usual ordered-sector
--   integrand of the grown `Forest` representative, in list simplex coordinates.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/ChosenGrowth.lean#L136-L150
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/ChosenGrowth.lean#L136-L150

import Definitions.Def_BKAR_OrderedAssembly_CanonicalForestBridge
import Definitions.Def_BKAR_OrderedAssembly_ChosenGrowth
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.grownForestForSupportOrder_branchIntegrand_eq_orderedSectorIntegrand
    (choices : ActiveExtensionChoice V)
    (I : ForestIndex V)
    (order : {order : List (Edge V) // order ∈ edgeSetOrders I.edges})
    (ρ : (Edge V → ℝ) → ℝ)
    (ts : List ℝ) (hlen : ts.length = order.val.length) :
    (grownForestForSupportOrder_orderedGrowth choices I order).branchIntegrand
        emptyParam ρ ts =
      mixedPartialList order.val.reverse ρ
        ((grownForestForSupportOrder choices I order).standardInterp
          ((grownForestForSupportOrder choices I order).paramsOfOrder
            order.val ts)) := by sorry
