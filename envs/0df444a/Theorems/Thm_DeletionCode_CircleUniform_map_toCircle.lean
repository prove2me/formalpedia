-- Prove2me | Theorems.Thm_DeletionCode_CircleUniform_map_toCircle
-- name    : DeletionCode.CircleUniform.map_toCircle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:16:59.097611+00:00
-- url     : https://prove2.me/theorems/d72e26d7-dc8b-4cc1-a327-5a4f095aa63f
-- title:
--   Circle Uniform: map to Circle
-- statement:
--   The Circle Uniform construction uses the map to Circle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CircleUniform.lean#L92-L94
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CircleUniform.lean#L92-L94

import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_DeletionCode_CircleUniform
set_option autoImplicit true
open DeletionCode DeletionCode.CircleUniform
open MeasureTheory Set
open scoped ENNReal

theorem DeletionCode.CircleUniform.map_toCircle (I : Type*) [Fintype I] :
    Measure.map (@toCircle I) (realWeights I) = volume := by sorry
