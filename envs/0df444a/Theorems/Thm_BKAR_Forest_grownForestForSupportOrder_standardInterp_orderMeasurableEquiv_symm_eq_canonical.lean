-- Prove2me | Theorems.Thm_BKAR_Forest_grownForestForSupportOrder_standardInterp_orderMeasurableEquiv_symm_eq_canonical
-- name    : BKAR.Forest.grownForestForSupportOrder_standardInterp_orderMeasurableEquiv_symm_eq_canonical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:02:41.454961+00:00
-- url     : https://prove2.me/theorems/73eac900-9aae-57ed-af5c-b79c6a1bc4d8
-- title:
--   Forest: grown Forest For Support Order standard Interp order Measurable Equiv symm eq canonical
-- statement:
--   The grown forest for a support/order and the canonical grown
--   representative have the same finite-coordinate interpolation point on that
--   support/order sector.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/CanonicalSector.lean#L155-L189
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/CanonicalSector.lean#L155-L189

import Definitions.Def_BKAR_OrderedAssembly_ChosenGrowth
import Definitions.Def_BKAR_CubePartition_SimplexSector_Finite
import Definitions.Def_BKAR_OrderedAssembly_CanonicalSector
import Theorems.Thm_BKAR_Forest_canonicalGrownForestForSupport_order_mem_edgeOrders
import Theorems.Thm_BKAR_Forest_grownForestForSupportOrder_order_mem_edgeOrders

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.grownForestForSupportOrder_standardInterp_orderMeasurableEquiv_symm_eq_canonical
    (choices : ActiveExtensionChoice V)
    (I : ForestIndex V)
    (order : {order : List (Edge V) // order ∈ edgeSetOrders I.edges})
    (ts : Fin order.val.length → ℝ) :
    (grownForestForSupportOrder choices I order).standardInterp
        ((Forest.orderMeasurableEquivOfOrder
            (grownForestForSupportOrder choices I order)
            (grownForestForSupportOrder_order_mem_edgeOrders
              choices I order)).symm ts) =
      (canonicalGrownForestForSupport choices I).standardInterp
        ((Forest.orderMeasurableEquivOfOrder
            (canonicalGrownForestForSupport choices I)
            (canonicalGrownForestForSupport_order_mem_edgeOrders
              choices I order.property)).symm ts) := by sorry
