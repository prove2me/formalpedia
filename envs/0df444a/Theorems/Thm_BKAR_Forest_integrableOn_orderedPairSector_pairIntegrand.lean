-- Prove2me | Theorems.Thm_BKAR_Forest_integrableOn_orderedPairSector_pairIntegrand
-- name    : BKAR.Forest.integrableOn_orderedPairSector_pairIntegrand
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:11:29.274825+00:00
-- url     : https://prove2.me/theorems/a0cc5f12-81af-4e98-a7c3-23c9ec65d064
-- title:
--   Forest: integrable On ordered Pair Sector pair Integrand
-- statement:
--   The Forest construction uses the integrable On ordered Pair Sector pair Integrand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Pair.lean#L464-L500
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Pair.lean#L464-L500

import Definitions.Def_BKAR_CubePartition_SimplexSector_Equiv
import Definitions.Def_BKAR_CubePartition_SimplexSector_Pair
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.integrableOn_orderedPairSector_pairIntegrand
    (F : Forest V) {e₁ e₂ : Edge V} (horder : [e₁, e₂] ∈ F.edgeOrders)
    (ρ : (Edge V → ℝ) → ℝ) (hρ : BKARContDiff ρ) :
    IntegrableOn
      (fun z : ℝ × ℝ =>
        mixedPartialList [e₁, e₂].reverse ρ
          (F.standardInterp
            ((F.pairMeasurableEquivOfPair
              (F.edges_eq_pair_of_pair_mem_edgeOrders horder)
              (F.ne_of_pair_mem_edgeOrders horder)).symm z)))
      orderedPairSector := by sorry
