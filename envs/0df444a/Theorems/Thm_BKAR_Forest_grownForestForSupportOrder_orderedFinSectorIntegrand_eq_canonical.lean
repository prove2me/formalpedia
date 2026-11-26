-- Prove2me | Theorems.Thm_BKAR_Forest_grownForestForSupportOrder_orderedFinSectorIntegrand_eq_canonical
-- name    : BKAR.Forest.grownForestForSupportOrder_orderedFinSectorIntegrand_eq_canonical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:02:59.330574+00:00
-- url     : https://prove2.me/theorems/9484caa4-f314-4e77-a4a9-cd3cd3917d4e
-- title:
--   Forest: grown Forest For Support Order ordered Fin Sector Integrand eq canonical
-- statement:
--   Pointwise finite-sector integrands agree after replacing the support/order
--   grown forest by the canonical grown representative.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/CanonicalSector.lean#L195-L215
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/CanonicalSector.lean#L195-L215

import Definitions.Def_BKAR_OrderedAssembly_ChosenGrowth
import Definitions.Def_BKAR_CubePartition_SimplexSector_Finite
import Definitions.Def_BKAR_OrderedAssembly_CanonicalSector
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse
import Theorems.Thm_BKAR_Forest_canonicalGrownForestForSupport_order_mem_edgeOrders
import Theorems.Thm_BKAR_Forest_grownForestForSupportOrder_order_mem_edgeOrders

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.grownForestForSupportOrder_orderedFinSectorIntegrand_eq_canonical
    (choices : ActiveExtensionChoice V)
    (I : ForestIndex V)
    (order : {order : List (Edge V) // order ∈ edgeSetOrders I.edges})
    (ρ : (Edge V → ℝ) → ℝ)
    (ts : Fin order.val.length → ℝ) :
    mixedPartialList order.val.reverse ρ
        ((grownForestForSupportOrder choices I order).standardInterp
          ((Forest.orderMeasurableEquivOfOrder
              (grownForestForSupportOrder choices I order)
              (grownForestForSupportOrder_order_mem_edgeOrders
                choices I order)).symm ts)) =
      mixedPartialList order.val.reverse ρ
        ((canonicalGrownForestForSupport choices I).standardInterp
          ((Forest.orderMeasurableEquivOfOrder
              (canonicalGrownForestForSupport choices I)
              (canonicalGrownForestForSupport_order_mem_edgeOrders
                choices I order.property)).symm ts)) := by sorry
