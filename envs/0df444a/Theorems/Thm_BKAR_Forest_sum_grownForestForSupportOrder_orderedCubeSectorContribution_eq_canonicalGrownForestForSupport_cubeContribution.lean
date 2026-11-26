-- Prove2me | Theorems.Thm_BKAR_Forest_sum_grownForestForSupportOrder_orderedCubeSectorContribution_eq_canonicalGrownForestForSupport_cubeContribution
-- name    : BKAR.Forest.sum_grownForestForSupportOrder_orderedCubeSectorContribution_eq_canonicalGrownForestForSupport_cubeContribution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:01:54.008191+00:00
-- url     : https://prove2.me/theorems/5cfd2498-8d1e-5f84-bb73-80c0018f06d6
-- title:
--   Forest: sum grown Forest For Support Order ordered Cube Sector Contribution eq canonical Grown Forest For Support cube Contribution
-- statement:
--   After sectorwise canonicalization, the whole support/order sum over grown
--   `Forest` representatives folds to the ordinary cube contribution of the canonical grown
--   representative.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/CubeFold.lean#L124-L159
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/CubeFold.lean#L124-L159

import Definitions.Def_BKAR_CubePartition_MeasureSmoothness
import Definitions.Def_BKAR_OrderedAssembly_CanonicalSector
import Definitions.Def_BKAR_OrderedAssembly_CubeFold
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.sum_grownForestForSupportOrder_orderedCubeSectorContribution_eq_canonicalGrownForestForSupport_cubeContribution
    (choices : ActiveExtensionChoice V) (I : ForestIndex V)
    (ρ : (Edge V → ℝ) → ℝ) (hρ : BKARContDiff ρ) :
    Finset.sum (edgeSetOrders I.edges).attach
      (fun order =>
        (grownForestForSupportOrder choices I order).orderedCubeSectorContribution
          order.val ρ) =
      (canonicalGrownForestForSupport choices I).cubeContribution ρ := by sorry
