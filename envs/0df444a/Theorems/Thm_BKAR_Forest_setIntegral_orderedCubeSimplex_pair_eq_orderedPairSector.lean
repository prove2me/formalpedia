-- Prove2me | Theorems.Thm_BKAR_Forest_setIntegral_orderedCubeSimplex_pair_eq_orderedPairSector
-- name    : BKAR.Forest.setIntegral_orderedCubeSimplex_pair_eq_orderedPairSector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:09:54.883174+00:00
-- url     : https://prove2.me/theorems/771d2506-c787-5407-ab79-a46464c1a7c1
-- title:
--   Forest: set Integral ordered Cube Simplex pair eq ordered Pair Sector
-- statement:
--   Two-edge simplex-sector coordinate transport: integrating over the ordered
--   cube sector is
--   the same as integrating over the explicit pair-coordinate sector, with the
--   integrand pulled back by the inverse coordinate equivalence.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Pair.lean#L371-L402
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Pair.lean#L371-L402

import Definitions.Def_BKAR_CubePartition_SimplexSector_Equiv
import Definitions.Def_BKAR_CubePartition_SimplexSector_Pair
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.setIntegral_orderedCubeSimplex_pair_eq_orderedPairSector
    (F : Forest V) {e₁ e₂ : Edge V} (horder : [e₁, e₂] ∈ F.edgeOrders)
    (g : (F.EdgeParam → ℝ) → ℝ) :
    ∫ u in F.orderedCubeSimplex [e₁, e₂], g u
        ∂(volume : Measure (F.EdgeParam → ℝ)) =
      ∫ z in orderedPairSector,
        g ((F.pairMeasurableEquivOfPair
          (F.edges_eq_pair_of_pair_mem_edgeOrders horder)
          (F.ne_of_pair_mem_edgeOrders horder)).symm z) := by sorry
