-- Prove2me | Theorems.Thm_BKAR_Forest_paramsOfOrder_pair_eq_pairMeasurableEquivOfPair_symm
-- name    : BKAR.Forest.paramsOfOrder_pair_eq_pairMeasurableEquivOfPair_symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:10:24.5158+00:00
-- url     : https://prove2.me/theorems/9ed6adf4-e5c7-4676-ac1f-e32aa7245322
-- title:
--   Forest: params Of Order pair eq pair Measurable Equiv Of Pair symm
-- statement:
--   The Forest construction uses the params Of Order pair eq pair Measurable Equiv Of Pair symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Pair.lean#L260-L290
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Pair.lean#L260-L290

import Definitions.Def_BKAR_CubePartition_SimplexSector_Equiv
import Definitions.Def_BKAR_CubePartition_SimplexSector_Pair
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.paramsOfOrder_pair_eq_pairMeasurableEquivOfPair_symm
    (F : Forest V) {e₁ e₂ : Edge V}
    (hedges : F.edges = ({e₁, e₂} : Finset (Edge V))) (hne : e₁ ≠ e₂)
    (z : ℝ × ℝ) :
    F.paramsOfOrder [e₁, e₂] [z.1, z.2] =
      (F.pairMeasurableEquivOfPair hedges hne).symm z := by sorry
