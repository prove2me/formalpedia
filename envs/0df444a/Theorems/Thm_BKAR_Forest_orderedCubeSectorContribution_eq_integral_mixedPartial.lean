-- Prove2me | Theorems.Thm_BKAR_Forest_orderedCubeSectorContribution_eq_integral_mixedPartial
-- name    : BKAR.Forest.orderedCubeSectorContribution_eq_integral_mixedPartial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:07:02.433324+00:00
-- url     : https://prove2.me/theorems/bb036495-e729-40ba-81fd-1932c49908dd
-- title:
--   Forest: ordered Cube Sector Contribution eq integral mixed Partial
-- statement:
--   On a canonical ordered sector, the order-specific recursive mixed partial is
--   the same as the unordered forest mixed partial. This is the analytic half of
--   the sector-to-cube bridge.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/MeasureSmoothness.lean#L98-L106
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/MeasureSmoothness.lean#L98-L106

import Definitions.Def_BKAR_CubePartition_MeasurePartition
import Definitions.Def_BKAR_PartialDerivSymmetry
import Definitions.Def_BKAR_CubePartition_MeasureSmoothness
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.orderedCubeSectorContribution_eq_integral_mixedPartial
    (F : Forest V) {order : List (Edge V)} (horder : order ∈ F.edgeOrders)
    (ρ : (Edge V → ℝ) → ℝ) (hρ : BKARContDiff ρ) :
    F.orderedCubeSectorContribution order ρ =
      ∫ u in F.orderedCubeSimplex order,
        F.mixedPartial ρ (F.standardInterp u)
          ∂(volume : Measure (F.EdgeParam → ℝ)) := by sorry
