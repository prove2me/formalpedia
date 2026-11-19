-- Prove2me | Theorems.Thm_DeletionCode_CircleUniform_measurePreserving_realUnit
-- name    : DeletionCode.CircleUniform.measurePreserving_realUnit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:07:39.856722+00:00
-- url     : https://prove2.me/theorems/34885f3d-86fd-44c2-be9d-3826be1f945b
-- title:
--   Circle Uniform: measure Preserving real Unit
-- statement:
--   The covering map has the correct law for [0,1), not only for the
--   (0,1] fundamental domain used by the standard library.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CircleUniform.lean#L62-L66
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CircleUniform.lean#L62-L66

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

theorem DeletionCode.CircleUniform.measurePreserving_realUnit :
    MeasurePreserving (fun r : ℝ => (r : UnitAddCircle)) realUnit volume := by sorry
