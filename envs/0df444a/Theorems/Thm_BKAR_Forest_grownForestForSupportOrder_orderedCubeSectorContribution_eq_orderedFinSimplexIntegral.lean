-- Prove2me | Theorems.Thm_BKAR_Forest_grownForestForSupportOrder_orderedCubeSectorContribution_eq_orderedFinSimplexIntegral
-- name    : BKAR.Forest.grownForestForSupportOrder_orderedCubeSectorContribution_eq_orderedFinSimplexIntegral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:00:34.359956+00:00
-- url     : https://prove2.me/theorems/bd44b696-6e38-56d5-954b-abfa3ad6e164
-- title:
--   Forest: grown Forest For Support Order ordered Cube Sector Contribution eq ordered Fin Simplex Integral
-- statement:
--   Finite-coordinate form of the grown support/order cube sector, written
--   directly with the grown forest's ordered-sector integrand.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/CanonicalSector.lean#L73-L89
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/CanonicalSector.lean#L73-L89

import Definitions.Def_BKAR_OrderedAssembly_ChosenGrowth
import Definitions.Def_BKAR_CubePartition_SimplexSector_Finite
import Definitions.Def_BKAR_OrderedAssembly_CanonicalSector
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse
import Theorems.Thm_BKAR_Forest_grownForestForSupportOrder_order_mem_edgeOrders

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.grownForestForSupportOrder_orderedCubeSectorContribution_eq_orderedFinSimplexIntegral
    (choices : ActiveExtensionChoice V)
    (I : ForestIndex V)
    (order : {order : List (Edge V) // order ∈ edgeSetOrders I.edges})
    (ρ : (Edge V → ℝ) → ℝ) :
    (grownForestForSupportOrder choices I order).orderedCubeSectorContribution
        order.val ρ =
      ∫ ts in orderedFinSimplex order.val.length,
        mixedPartialList order.val.reverse ρ
          ((grownForestForSupportOrder choices I order).standardInterp
            ((Forest.orderMeasurableEquivOfOrder
                (grownForestForSupportOrder choices I order)
                (grownForestForSupportOrder_order_mem_edgeOrders
                  choices I order)).symm ts)) := by sorry
