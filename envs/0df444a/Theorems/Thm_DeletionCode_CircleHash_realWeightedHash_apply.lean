-- Prove2me | Theorems.Thm_DeletionCode_CircleHash_realWeightedHash_apply
-- name    : DeletionCode.CircleHash.realWeightedHash_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:28:42.61136+00:00
-- url     : https://prove2.me/theorems/289eb1c7-efe5-45b6-a57d-58c42719ccbd
-- title:
--   Circle Hash: real Weighted Hash apply
-- statement:
--   The Circle Hash construction uses the real Weighted Hash apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CircleHash.lean#L107-L121
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CircleHash.lean#L107-L121

import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Algebra.Order.Floor.Ring
import Definitions.Def_DeletionCode_CircleHash
set_option autoImplicit true
open DeletionCode DeletionCode.CircleHash
open scoped BigOperators

theorem DeletionCode.CircleHash.realWeightedHash_apply {I : Type*} [Fintype I]
    (weights : I → ℝ) (p : I → ℤ) :
    realWeightedHash weights p = ((∑ g, weights g * (p g : ℝ) : ℝ) : UnitAddCircle) := by sorry
