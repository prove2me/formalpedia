-- Prove2me | Theorems.Thm_DeletionCode_CircleUniform_measurableSet_smallArc
-- name    : DeletionCode.CircleUniform.measurableSet_smallArc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:37:06.68521+00:00
-- url     : https://prove2.me/theorems/1e591c67-de02-4ace-a6b5-5a98f97b462a
-- title:
--   Circle Uniform: measurable Set small Arc
-- statement:
--   The Circle Uniform construction uses the measurable Set small Arc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CircleUniform.lean#L28-L30
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CircleUniform.lean#L28-L30

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

theorem DeletionCode.CircleUniform.measurableSet_smallArc (Q : ℕ) : MeasurableSet (smallArc Q) := by sorry
