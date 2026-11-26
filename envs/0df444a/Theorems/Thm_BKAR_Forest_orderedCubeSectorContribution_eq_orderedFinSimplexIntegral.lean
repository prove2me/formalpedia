-- Prove2me | Theorems.Thm_BKAR_Forest_orderedCubeSectorContribution_eq_orderedFinSimplexIntegral
-- name    : BKAR.Forest.orderedCubeSectorContribution_eq_orderedFinSimplexIntegral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:10:12.559841+00:00
-- url     : https://prove2.me/theorems/3ffb6934-ed26-4904-b900-8514a19ca7ad
-- title:
--   Forest: ordered Cube Sector Contribution eq ordered Fin Simplex Integral
-- statement:
--   Arbitrary-order cube-sector contribution in finite ordered coordinates.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Finite.lean#L590-L600
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Finite.lean#L590-L600

import Definitions.Def_BKAR_CubePartition_SimplexSector
import Definitions.Def_BKAR_CubePartition_SimplexSector_Finite
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.orderedCubeSectorContribution_eq_orderedFinSimplexIntegral
    (F : Forest V) {order : List (Edge V)} (horder : order ∈ F.edgeOrders)
    (ρ : (Edge V → ℝ) → ℝ) :
    F.orderedCubeSectorContribution order ρ =
      ∫ ts in orderedFinSimplex order.length,
        mixedPartialList order.reverse ρ
          (F.standardInterp
            ((F.orderMeasurableEquivOfOrder horder).symm ts)) := by sorry
