-- Prove2me | Theorems.Thm_BKAR_Forest_orderedContribution_pair_eq_orderedCubeSectorContribution
-- name    : BKAR.Forest.orderedContribution_pair_eq_orderedCubeSectorContribution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:38:01.731394+00:00
-- url     : https://prove2.me/theorems/e5e1880e-f335-53bf-8c30-23ed9a4d9013
-- title:
--   Forest: ordered Contribution pair eq ordered Cube Sector Contribution
-- statement:
--   The Forest construction uses the ordered Contribution pair eq ordered Cube Sector Contribution property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Pair.lean#L502-L525
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Pair.lean#L502-L525

import Definitions.Def_BKAR_CubePartition_SimplexSector_Equiv
import Definitions.Def_BKAR_CubePartition_SimplexSector_Pair
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.orderedContribution_pair_eq_orderedCubeSectorContribution
    (F : Forest V) {e₁ e₂ : Edge V} (horder : [e₁, e₂] ∈ F.edgeOrders)
    (ρ : (Edge V → ℝ) → ℝ) (hρ : BKARContDiff ρ) :
    F.orderedContribution [e₁, e₂] ρ =
      F.orderedCubeSectorContribution [e₁, e₂] ρ := by sorry
