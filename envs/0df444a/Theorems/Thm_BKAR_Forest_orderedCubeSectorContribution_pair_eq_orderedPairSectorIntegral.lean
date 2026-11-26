-- Prove2me | Theorems.Thm_BKAR_Forest_orderedCubeSectorContribution_pair_eq_orderedPairSectorIntegral
-- name    : BKAR.Forest.orderedCubeSectorContribution_pair_eq_orderedPairSectorIntegral
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:09:56.967898+00:00
-- url     : https://prove2.me/theorems/68d9f0ba-8939-592a-b5a3-fe5fc3faf66e
-- title:
--   Forest: ordered Cube Sector Contribution pair eq ordered Pair Sector Integral
-- statement:
--   The two-edge ordered cube contribution, rewritten in explicit pair
--   coordinates. This is the sector-side half of the two-dimensional
--   simplex-sector bridge.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Pair.lean#L409-L421
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Pair.lean#L409-L421

import Definitions.Def_BKAR_CubePartition_SimplexSector_Equiv
import Definitions.Def_BKAR_CubePartition_SimplexSector_Pair
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.orderedCubeSectorContribution_pair_eq_orderedPairSectorIntegral
    (F : Forest V) {e₁ e₂ : Edge V} (horder : [e₁, e₂] ∈ F.edgeOrders)
    (ρ : (Edge V → ℝ) → ℝ) :
    F.orderedCubeSectorContribution [e₁, e₂] ρ =
      ∫ z in orderedPairSector,
        mixedPartialList [e₁, e₂].reverse ρ
          (F.standardInterp
            ((F.pairMeasurableEquivOfPair
              (F.edges_eq_pair_of_pair_mem_edgeOrders horder)
              (F.ne_of_pair_mem_edgeOrders horder)).symm z)) := by sorry
