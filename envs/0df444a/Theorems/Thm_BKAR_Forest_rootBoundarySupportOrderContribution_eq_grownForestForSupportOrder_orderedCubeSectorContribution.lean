-- Prove2me | Theorems.Thm_BKAR_Forest_rootBoundarySupportOrderContribution_eq_grownForestForSupportOrder_orderedCubeSectorContribution
-- name    : BKAR.Forest.rootBoundarySupportOrderContribution_eq_grownForestForSupportOrder_orderedCubeSectorContribution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:05:37.181233+00:00
-- url     : https://prove2.me/theorems/55726ace-1a32-49b1-933e-0eb4c02f3a78
-- title:
--   Forest: root Boundary Support Order Contribution eq grown Forest For Support Order ordered Cube Sector Contribution
-- statement:
--   Per-sector simplex-to-cube-sector bridge for the root support/order fiber:
--   the recursive ordered
--   simplex contribution is the corresponding closed cube-sector integral of the
--   `Forest` representative grown by following that same support order.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/CanonicalSector.lean#L97-L111
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/CanonicalSector.lean#L97-L111

import Definitions.Def_BKAR_OrderedAssembly_ChosenGrowth
import Definitions.Def_BKAR_CubePartition_SimplexSector_Finite
import Definitions.Def_BKAR_OrderedAssembly_CanonicalSector
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.rootBoundarySupportOrderContribution_eq_grownForestForSupportOrder_orderedCubeSectorContribution
    (choices : ActiveExtensionChoice V)
    (I : ForestIndex V)
    (order : {order : List (Edge V) // order ∈ edgeSetOrders I.edges})
    (ρ : (Edge V → ℝ) → ℝ) (hρ : BKARContDiff ρ) :
    rootBoundarySupportOrderContribution choices ρ I order.val =
      (grownForestForSupportOrder choices I order).orderedCubeSectorContribution
        order.val ρ := by sorry
