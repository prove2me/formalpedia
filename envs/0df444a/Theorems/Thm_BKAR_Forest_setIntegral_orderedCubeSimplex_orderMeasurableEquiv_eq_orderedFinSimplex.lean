-- Prove2me | Theorems.Thm_BKAR_Forest_setIntegral_orderedCubeSimplex_orderMeasurableEquiv_eq_orderedFinSimplex
-- name    : BKAR.Forest.setIntegral_orderedCubeSimplex_orderMeasurableEquiv_eq_orderedFinSimplex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:37:01.962847+00:00
-- url     : https://prove2.me/theorems/50a79045-24e4-52a0-a19a-486f3cf97498
-- title:
--   Forest: set Integral ordered Cube Simplex order Measurable Equiv eq ordered Fin Simplex
-- statement:
--   Measure transport for arbitrary canonical orders, for integrands already
--   written in ordered finite coordinates.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Equiv.lean#L272-L287
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Equiv.lean#L272-L287

import Definitions.Def_BKAR_CubePartition_SimplexSector_Singleton
import Definitions.Def_BKAR_CubePartition_SimplexSector_Equiv
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.setIntegral_orderedCubeSimplex_orderMeasurableEquiv_eq_orderedFinSimplex
    (F : Forest V) {order : List (Edge V)} (horder : order ∈ F.edgeOrders)
    (g : (Fin order.length → ℝ) → ℝ) :
    ∫ u in F.orderedCubeSimplex order,
        g (F.orderMeasurableEquivOfOrder horder u)
        ∂(volume : Measure (F.EdgeParam → ℝ)) =
      ∫ ts in orderedFinSimplex order.length, g ts := by sorry
