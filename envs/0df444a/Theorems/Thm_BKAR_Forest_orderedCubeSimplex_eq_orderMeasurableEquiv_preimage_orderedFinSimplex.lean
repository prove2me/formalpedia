-- Prove2me | Theorems.Thm_BKAR_Forest_orderedCubeSimplex_eq_orderMeasurableEquiv_preimage_orderedFinSimplex
-- name    : BKAR.Forest.orderedCubeSimplex_eq_orderMeasurableEquiv_preimage_orderedFinSimplex
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:56:46.150148+00:00
-- url     : https://prove2.me/theorems/07eaab03-fd15-5779-86d8-a9918713c05c
-- title:
--   Forest: ordered Cube Simplex eq order Measurable Equiv preimage ordered Fin Simplex
-- statement:
--   Set-level arbitrary-order simplex-sector bridge: a canonical ordered cube
--   sector is the
--   preimage of the standard ordered finite simplex under the ordered coordinate
--   equivalence.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Equiv.lean#L230-L266
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Equiv.lean#L230-L266

import Definitions.Def_BKAR_CubePartition_SimplexSector_Singleton
import Definitions.Def_BKAR_CubePartition_SimplexSector_Equiv
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.orderedCubeSimplex_eq_orderMeasurableEquiv_preimage_orderedFinSimplex
    (F : Forest V) {order : List (Edge V)} (horder : order ∈ F.edgeOrders) :
    F.orderedCubeSimplex order =
      (F.orderMeasurableEquivOfOrder horder) ⁻¹'
        orderedFinSimplex order.length := by sorry
