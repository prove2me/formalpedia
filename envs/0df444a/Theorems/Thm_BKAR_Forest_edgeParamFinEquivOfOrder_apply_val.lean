-- Prove2me | Theorems.Thm_BKAR_Forest_edgeParamFinEquivOfOrder_apply_val
-- name    : BKAR.Forest.edgeParamFinEquivOfOrder_apply_val
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:55:05.83486+00:00
-- url     : https://prove2.me/theorems/14510faa-3c3b-5ad2-a0f6-fb0e683ecd48
-- title:
--   Forest: edge Param Fin Equiv Of Order apply val
-- statement:
--   The Forest construction uses the edge Param Fin Equiv Of Order apply val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Equiv.lean#L59-L63
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Equiv.lean#L59-L63

import Definitions.Def_BKAR_CubePartition_SimplexSector_Singleton
import Definitions.Def_BKAR_CubePartition_SimplexSector_Equiv
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.edgeParamFinEquivOfOrder_apply_val
    (F : Forest V) {order : List (Edge V)} (horder : order ∈ F.edgeOrders)
    (i : Fin order.length) :
    (F.edgeParamFinEquivOfOrder horder i).val = order.get i := by sorry

attribute [defeq] BKAR.Forest.edgeParamFinEquivOfOrder_apply_val
