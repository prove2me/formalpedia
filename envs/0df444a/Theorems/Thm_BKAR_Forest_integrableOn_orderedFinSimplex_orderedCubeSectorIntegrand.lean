-- Prove2me | Theorems.Thm_BKAR_Forest_integrableOn_orderedFinSimplex_orderedCubeSectorIntegrand
-- name    : BKAR.Forest.integrableOn_orderedFinSimplex_orderedCubeSectorIntegrand
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:41:10.204034+00:00
-- url     : https://prove2.me/theorems/0945ac77-caea-5774-80e4-5b9e0a000c76
-- title:
--   Forest: integrable On ordered Fin Simplex ordered Cube Sector Integrand
-- statement:
--   The actual BKAR sector integrand is integrable on the finite ordered simplex
--   under the global smoothness hypothesis.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Finite.lean#L606-L641
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Finite.lean#L606-L641

import Definitions.Def_BKAR_CubePartition_SimplexSector
import Definitions.Def_BKAR_CubePartition_SimplexSector_Finite
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.integrableOn_orderedFinSimplex_orderedCubeSectorIntegrand
    (F : Forest V) {order : List (Edge V)} (horder : order ∈ F.edgeOrders)
    (ρ : (Edge V → ℝ) → ℝ) (hρ : BKARContDiff ρ) :
    IntegrableOn
      (fun ts : Fin order.length → ℝ =>
        mixedPartialList order.reverse ρ
          (F.standardInterp
            ((F.orderMeasurableEquivOfOrder horder).symm ts)))
      (orderedFinSimplex order.length) := by sorry
