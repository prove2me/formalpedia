-- Prove2me | Theorems.Thm_BKAR_Forest_cubeContribution_eq_sum_orderedCubeSectorContribution
-- name    : BKAR.Forest.cubeContribution_eq_sum_orderedCubeSectorContribution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:10:44.380136+00:00
-- url     : https://prove2.me/theorems/b79b2d71-2994-4f9f-a911-db2d06e1cf28
-- title:
--   Forest: cube Contribution eq sum ordered Cube Sector Contribution
-- statement:
--   The unit-cube partition step plus mixed-partial order independence: the
--   usual unordered cube
--   contribution is the sum of the order-specific closed cube-sector
--   contributions.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/MeasureSmoothness.lean#L114-L143
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/MeasureSmoothness.lean#L114-L143

import Definitions.Def_BKAR_CubePartition_MeasurePartition
import Definitions.Def_BKAR_PartialDerivSymmetry
import Definitions.Def_BKAR_CubePartition_MeasureSmoothness
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.cubeContribution_eq_sum_orderedCubeSectorContribution
    (F : Forest V) (ρ : (Edge V → ℝ) → ℝ)
    (hρ : BKARContDiff ρ) :
    F.cubeContribution ρ =
      Finset.sum F.edgeOrders
        (fun order => F.orderedCubeSectorContribution order ρ) := by sorry
