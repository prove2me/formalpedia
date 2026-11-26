-- Prove2me | Theorems.Thm_BKAR_Forest_orderedCubeSimplex_pair_eq_pairCoord_preimage_orderedPairSector
-- name    : BKAR.Forest.orderedCubeSimplex_pair_eq_pairCoord_preimage_orderedPairSector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:09:50.150412+00:00
-- url     : https://prove2.me/theorems/bf764566-11b3-50e0-aef3-fa1aef275ed0
-- title:
--   Forest: ordered Cube Simplex pair eq pair Coord preimage ordered Pair Sector
-- statement:
--   The Forest construction uses the ordered Cube Simplex pair eq pair Coord preimage ordered Pair Sector property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Pair.lean#L329-L350
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Pair.lean#L329-L350

import Definitions.Def_BKAR_CubePartition_SimplexSector_Equiv
import Definitions.Def_BKAR_CubePartition_SimplexSector_Pair
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.orderedCubeSimplex_pair_eq_pairCoord_preimage_orderedPairSector
    (F : Forest V) {e₁ e₂ : Edge V} (horder : [e₁, e₂] ∈ F.edgeOrders) :
    F.orderedCubeSimplex [e₁, e₂] =
      (F.pairCoordOfOrder e₁ e₂) ⁻¹' orderedPairSector := by sorry
