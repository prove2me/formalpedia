-- Prove2me | Theorems.Thm_BKAR_Forest_sectorOrderRel_isAntisymm_of_notMem_collisionSet
-- name    : BKAR.Forest.sectorOrderRel_isAntisymm_of_notMem_collisionSet
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:50:42.803274+00:00
-- url     : https://prove2.me/theorems/d76d0ff2-7a5d-41c8-be93-a87dde74cb6c
-- title:
--   Forest: sector Order Rel is Antisymm of not Mem collision Set
-- statement:
--   The Forest construction uses the sector Order Rel is Antisymm of not Mem collision Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/MeasurePartition.lean#L107-L130
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/MeasurePartition.lean#L107-L130

import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Definitions.Def_BKAR_CubePartition_CubeIntegral
import Definitions.Def_BKAR_CubePartition_MeasurePartition
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.sectorOrderRel_isAntisymm_of_notMem_collisionSet
    (F : Forest V) {u : F.EdgeParam → ℝ}
    (hno : u ∉ F.collisionSet) :
    Std.Antisymm (F.sectorOrderRel u) := by sorry
