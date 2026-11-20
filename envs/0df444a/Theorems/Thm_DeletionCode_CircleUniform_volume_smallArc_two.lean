-- Prove2me | Theorems.Thm_DeletionCode_CircleUniform_volume_smallArc_two
-- name    : DeletionCode.CircleUniform.volume_smallArc_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:16:59.949731+00:00
-- url     : https://prove2.me/theorems/2b8b739f-602c-4228-86d2-3709f8059394
-- title:
--   Circle Uniform: volume small Arc two
-- statement:
--   For Q=2 the open test has full measure, although it excludes the
--   half-turn itself. No incorrect equality of the underlying sets is used.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CircleUniform.lean#L51-L52
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CircleUniform.lean#L51-L52

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

theorem DeletionCode.CircleUniform.volume_smallArc_two : volume (smallArc 2) = 1 := by sorry
