-- Prove2me | Theorems.Thm_BKAR_Forest_map_paramValue_eq_ofFn_orderMeasurableEquiv
-- name    : BKAR.Forest.map_paramValue_eq_ofFn_orderMeasurableEquiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:08:43.99985+00:00
-- url     : https://prove2.me/theorems/feb52c79-5d41-5f24-8a26-77934e6a79f2
-- title:
--   Forest: map param Value eq of Fn order Measurable Equiv
-- statement:
--   Reading an arbitrary cube point in canonical order gives the corresponding `ofFn` list.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Equiv.lean#L212-L222
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Equiv.lean#L212-L222

import Definitions.Def_BKAR_CubePartition_SimplexSector_Singleton
import Definitions.Def_BKAR_CubePartition_SimplexSector_Equiv
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.map_paramValue_eq_ofFn_orderMeasurableEquiv
    (F : Forest V) {order : List (Edge V)} (horder : order ∈ F.edgeOrders)
    (u : F.EdgeParam → ℝ) :
    order.map (F.paramValue u) =
      List.ofFn (F.orderMeasurableEquivOfOrder horder u) := by sorry
