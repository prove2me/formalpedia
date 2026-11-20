-- Prove2me | Theorems.Thm_DeletionCode_CircleHash_norm_coe_le_integer_distance
-- name    : DeletionCode.CircleHash.norm_coe_le_integer_distance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:16:20.09271+00:00
-- url     : https://prove2.me/theorems/7fdc5e0d-38d0-4fa7-b574-658a30a2503b
-- title:
--   Circle Hash: norm coe le integer distance
-- statement:
--   The Circle Hash construction uses the norm coe le integer distance property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CircleHash.lean#L90-L93
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CircleHash.lean#L90-L93

import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Algebra.Order.Floor.Ring
import Definitions.Def_DeletionCode_CircleHash
set_option autoImplicit true
open DeletionCode DeletionCode.CircleHash
open scoped BigOperators

theorem DeletionCode.CircleHash.norm_coe_le_integer_distance (r : ℝ) (z : ℤ) :
    ‖(r : UnitAddCircle)‖ ≤ |r - (z : ℝ)| := by sorry
