-- Prove2me | Theorems.Thm_BKAR_Forest_cubeContribution_eq_sum_orderedCubeSimplex_mixedPartial
-- name    : BKAR.Forest.cubeContribution_eq_sum_orderedCubeSimplex_mixedPartial
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:05:25.546731+00:00
-- url     : https://prove2.me/theorems/0b2df2ec-5283-40d6-9b0f-839534576764
-- title:
--   Forest: cube Contribution eq sum ordered Cube Simplex mixed Partial
-- statement:
--   The unit-cube partition step for the usual unordered forest contribution:
--   the integral over `[0,1]^{E(F)}` is the finite sum of its closed ordered
--   sectors; sector overlaps are null by the collision-hyperplane theorem.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/MeasureSmoothness.lean#L55-L70
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/MeasureSmoothness.lean#L55-L70

import Definitions.Def_BKAR_CubePartition_MeasurePartition
import Definitions.Def_BKAR_PartialDerivSymmetry
import Definitions.Def_BKAR_CubePartition_MeasureSmoothness
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.cubeContribution_eq_sum_orderedCubeSimplex_mixedPartial
    (F : Forest V) (ρ : (Edge V → ℝ) → ℝ)
    (hρ : BKARContDiff ρ) :
    F.cubeContribution ρ =
      Finset.sum
        (Finset.univ :
          Finset {order : List (Edge V) // order ∈ F.edgeOrders})
        (fun order =>
          ∫ u in F.orderedCubeSimplex order.val,
            F.mixedPartial ρ (F.standardInterp u)
              ∂(volume : Measure (F.EdgeParam → ℝ))) := by sorry
