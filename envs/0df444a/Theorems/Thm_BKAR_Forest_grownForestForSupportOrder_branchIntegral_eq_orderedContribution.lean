-- Prove2me | Theorems.Thm_BKAR_Forest_grownForestForSupportOrder_branchIntegral_eq_orderedContribution
-- name    : BKAR.Forest.grownForestForSupportOrder_branchIntegral_eq_orderedContribution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:01:28.902438+00:00
-- url     : https://prove2.me/theorems/d6f6f06f-333a-54e1-a63f-90134ba93a6c
-- title:
--   Forest: grown Forest For Support Order branch Integral eq ordered Contribution
-- statement:
--   The grown support/order forest's ordered contribution can be read as the
--   branch integral of its concrete ordered-growth certificate.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/ChosenGrowth.lean#L102-L112
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/ChosenGrowth.lean#L102-L112

import Definitions.Def_BKAR_OrderedAssembly_CanonicalForestBridge
import Definitions.Def_BKAR_OrderedAssembly_ChosenGrowth
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.grownForestForSupportOrder_branchIntegral_eq_orderedContribution
    (choices : ActiveExtensionChoice V)
    (I : ForestIndex V)
    (order : {order : List (Edge V) // order ∈ edgeSetOrders I.edges})
    (ρ : (Edge V → ℝ) → ℝ) :
  (grownForestForSupportOrder_orderedGrowth choices I order).branchIntegral
        emptyParam ρ =
      (grownForestForSupportOrder choices I order).orderedContribution
        order.val ρ := by sorry
