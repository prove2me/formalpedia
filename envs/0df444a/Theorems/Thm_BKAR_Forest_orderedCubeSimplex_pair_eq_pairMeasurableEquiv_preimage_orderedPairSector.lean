-- Prove2me | Theorems.Thm_BKAR_Forest_orderedCubeSimplex_pair_eq_pairMeasurableEquiv_preimage_orderedPairSector
-- name    : BKAR.Forest.orderedCubeSimplex_pair_eq_pairMeasurableEquiv_preimage_orderedPairSector
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:58:35.967609+00:00
-- url     : https://prove2.me/theorems/4cf971d6-46b1-4dad-b3c5-94ff56ca87a2
-- title:
--   Forest: ordered Cube Simplex pair eq pair Measurable Equiv preimage ordered Pair Sector
-- statement:
--   The Forest construction uses the ordered Cube Simplex pair eq pair Measurable Equiv preimage ordered Pair Sector property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Pair.lean#L352-L363
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Pair.lean#L352-L363

import Definitions.Def_BKAR_CubePartition_SimplexSector_Equiv
import Definitions.Def_BKAR_CubePartition_SimplexSector_Pair
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.orderedCubeSimplex_pair_eq_pairMeasurableEquiv_preimage_orderedPairSector
    (F : Forest V) {e₁ e₂ : Edge V} (horder : [e₁, e₂] ∈ F.edgeOrders) :
    F.orderedCubeSimplex [e₁, e₂] =
      (F.pairMeasurableEquivOfPair
        (F.edges_eq_pair_of_pair_mem_edgeOrders horder)
        (F.ne_of_pair_mem_edgeOrders horder)) ⁻¹' orderedPairSector := by sorry
