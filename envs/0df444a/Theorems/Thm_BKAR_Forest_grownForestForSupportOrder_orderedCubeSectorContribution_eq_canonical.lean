-- Prove2me | Theorems.Thm_BKAR_Forest_grownForestForSupportOrder_orderedCubeSectorContribution_eq_canonical
-- name    : BKAR.Forest.grownForestForSupportOrder_orderedCubeSectorContribution_eq_canonical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:00:37.721669+00:00
-- url     : https://prove2.me/theorems/9cf6a00d-66ea-5adc-ba9a-3c6c41ca2678
-- title:
--   Forest: grown Forest For Support Order ordered Cube Sector Contribution eq canonical
-- statement:
--   Sectorwise canonicalization: the closed cube-sector contribution of the
--   `Forest` representative grown by a support/order equals the same ordered sector of the
--   canonical grown representative for that support.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/CanonicalSector.lean#L222-L239
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/CanonicalSector.lean#L222-L239

import Definitions.Def_BKAR_OrderedAssembly_ChosenGrowth
import Definitions.Def_BKAR_CubePartition_SimplexSector_Finite
import Definitions.Def_BKAR_OrderedAssembly_CanonicalSector
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.grownForestForSupportOrder_orderedCubeSectorContribution_eq_canonical
    (choices : ActiveExtensionChoice V)
    (I : ForestIndex V)
    (order : {order : List (Edge V) // order ∈ edgeSetOrders I.edges})
    (ρ : (Edge V → ℝ) → ℝ) :
    (grownForestForSupportOrder choices I order).orderedCubeSectorContribution
        order.val ρ =
      (canonicalGrownForestForSupport choices I).orderedCubeSectorContribution
        order.val ρ := by sorry
