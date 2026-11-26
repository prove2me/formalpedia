-- Prove2me | Theorems.Thm_BKAR_Forest_grownForestForSupportOrder_orderedCubeSectorContribution_eq_integral_branchIntegrand
-- name    : BKAR.Forest.grownForestForSupportOrder_orderedCubeSectorContribution_eq_integral_branchIntegrand
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:05:04.785408+00:00
-- url     : https://prove2.me/theorems/982f4972-2542-4128-b744-9294dd149d5d
-- title:
--   Forest: grown Forest For Support Order ordered Cube Sector Contribution eq integral branch Integrand
-- statement:
--   Finite-sector normal form for the grown support/order forest, expressed via
--   its concrete chosen-growth branch integrand.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/CanonicalSector.lean#L56-L67
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/CanonicalSector.lean#L56-L67

import Definitions.Def_BKAR_OrderedAssembly_ChosenGrowth
import Definitions.Def_BKAR_CubePartition_SimplexSector_Finite
import Definitions.Def_BKAR_OrderedAssembly_CanonicalSector
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.grownForestForSupportOrder_orderedCubeSectorContribution_eq_integral_branchIntegrand
    (choices : ActiveExtensionChoice V)
    (I : ForestIndex V)
    (order : {order : List (Edge V) // order ∈ edgeSetOrders I.edges})
    (ρ : (Edge V → ℝ) → ℝ) :
    (grownForestForSupportOrder choices I order).orderedCubeSectorContribution
        order.val ρ =
      ∫ ts in orderedFinSimplex order.val.length,
        (grownForestForSupportOrder_orderedGrowth choices I order).branchIntegrand
          emptyParam ρ (List.ofFn ts) := by sorry
