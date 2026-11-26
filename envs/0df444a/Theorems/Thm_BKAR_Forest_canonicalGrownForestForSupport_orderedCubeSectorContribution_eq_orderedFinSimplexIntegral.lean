-- Prove2me | Theorems.Thm_BKAR_Forest_canonicalGrownForestForSupport_orderedCubeSectorContribution_eq_orderedFinSimplexIntegral
-- name    : BKAR.Forest.canonicalGrownForestForSupport_orderedCubeSectorContribution_eq_orderedFinSimplexIntegral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:02:27.889114+00:00
-- url     : https://prove2.me/theorems/06e12725-ae28-502d-bc0e-711303f1ff3e
-- title:
--   Forest: canonical Grown Forest For Support ordered Cube Sector Contribution eq ordered Fin Simplex Integral
-- statement:
--   Finite-coordinate form of the canonical grown representative's sector for
--   an arbitrary order of the same support.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/CanonicalSector.lean#L132-L148
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/CanonicalSector.lean#L132-L148

import Definitions.Def_BKAR_OrderedAssembly_ChosenGrowth
import Definitions.Def_BKAR_CubePartition_SimplexSector_Finite
import Definitions.Def_BKAR_OrderedAssembly_CanonicalSector
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse
import Theorems.Thm_BKAR_Forest_canonicalGrownForestForSupport_order_mem_edgeOrders

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.canonicalGrownForestForSupport_orderedCubeSectorContribution_eq_orderedFinSimplexIntegral
    (choices : ActiveExtensionChoice V) (I : ForestIndex V)
    (order : {order : List (Edge V) // order ∈ edgeSetOrders I.edges})
    (ρ : (Edge V → ℝ) → ℝ) :
    (canonicalGrownForestForSupport choices I).orderedCubeSectorContribution
        order.val ρ =
      ∫ ts in orderedFinSimplex order.val.length,
        mixedPartialList order.val.reverse ρ
          ((canonicalGrownForestForSupport choices I).standardInterp
            ((Forest.orderMeasurableEquivOfOrder
                (canonicalGrownForestForSupport choices I)
                (canonicalGrownForestForSupport_order_mem_edgeOrders
                  choices I order.property)).symm ts)) := by sorry
