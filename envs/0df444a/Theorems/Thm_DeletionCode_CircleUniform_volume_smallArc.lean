-- Prove2me | Theorems.Thm_DeletionCode_CircleUniform_volume_smallArc
-- name    : DeletionCode.CircleUniform.volume_smallArc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:36:17.291048+00:00
-- url     : https://prove2.me/theorems/4645eae1-2b76-42ff-8977-d5f626b0c976
-- title:
--   Circle Uniform: volume small Arc
-- statement:
--   Open and closed circle balls have equal Haar measure, so the strict
--   inequality loses no mass even at radius one half.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CircleUniform.lean#L34-L47
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CircleUniform.lean#L34-L47

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

theorem DeletionCode.CircleUniform.volume_smallArc (Q : ℕ) (hQ : 2 ≤ Q) :
    volume (smallArc Q) = ENNReal.ofReal (2 / (Q : ℝ)) := by sorry
