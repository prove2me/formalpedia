-- Prove2me | Theorems.Thm_BKAR_Forest_canonicalGrownForestForSupport_orderedCubeSectorContribution_eq_integral_branchIntegrand
-- name    : BKAR.Forest.canonicalGrownForestForSupport_orderedCubeSectorContribution_eq_integral_branchIntegrand
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:04:54.663445+00:00
-- url     : https://prove2.me/theorems/96b3ad9d-c5e1-4518-8641-2d62e617798a
-- title:
--   Forest: canonical Grown Forest For Support ordered Cube Sector Contribution eq integral branch Integrand
-- statement:
--   Finite-sector normal form for the canonical grown representative in its
--   canonical order.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/CanonicalSector.lean#L117-L126
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/CanonicalSector.lean#L117-L126

import Definitions.Def_BKAR_OrderedAssembly_ChosenGrowth
import Definitions.Def_BKAR_CubePartition_SimplexSector_Finite
import Definitions.Def_BKAR_OrderedAssembly_CanonicalSector
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.canonicalGrownForestForSupport_orderedCubeSectorContribution_eq_integral_branchIntegrand
    (choices : ActiveExtensionChoice V) (I : ForestIndex V)
    (ρ : (Edge V → ℝ) → ℝ) :
    (canonicalGrownForestForSupport choices I).orderedCubeSectorContribution
        I.canonicalOrder.val ρ =
      ∫ ts in orderedFinSimplex I.canonicalOrder.val.length,
        (canonicalGrownForestForSupport_orderedGrowth choices I).branchIntegrand
          emptyParam ρ (List.ofFn ts) := by sorry
