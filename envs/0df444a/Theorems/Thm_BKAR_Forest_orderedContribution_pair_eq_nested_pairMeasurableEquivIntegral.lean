-- Prove2me | Theorems.Thm_BKAR_Forest_orderedContribution_pair_eq_nested_pairMeasurableEquivIntegral
-- name    : BKAR.Forest.orderedContribution_pair_eq_nested_pairMeasurableEquivIntegral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:11:25.8055+00:00
-- url     : https://prove2.me/theorems/d02e6afc-6ae2-4376-a7b0-98e761d59bce
-- title:
--   Forest: ordered Contribution pair eq nested pair Measurable Equiv Integral
-- statement:
--   The two-edge recursive ordered contribution in the same explicit pair
--   coordinates as the cube-sector contribution. The remaining conversion step is the
--   ordinary triangular-domain integral theorem connecting this nested integral to
--   the set integral over `orderedPairSector`.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Pair.lean#L429-L462
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Pair.lean#L429-L462

import Definitions.Def_BKAR_CubePartition_SimplexSector_Equiv
import Definitions.Def_BKAR_CubePartition_SimplexSector_Pair
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.orderedContribution_pair_eq_nested_pairMeasurableEquivIntegral
    (F : Forest V) {e₁ e₂ : Edge V} (horder : [e₁, e₂] ∈ F.edgeOrders)
    (ρ : (Edge V → ℝ) → ℝ) :
    F.orderedContribution [e₁, e₂] ρ =
      ∫ t₁ in 0..(1 : ℝ), ∫ t₂ in 0..t₁,
        mixedPartialList [e₁, e₂].reverse ρ
          (F.standardInterp
            ((F.pairMeasurableEquivOfPair
              (F.edges_eq_pair_of_pair_mem_edgeOrders horder)
              (F.ne_of_pair_mem_edgeOrders horder)).symm (t₁, t₂))) := by sorry
