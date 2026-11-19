-- Prove2me | Theorems.Thm_DeletionCode_CircleHash_norm_coe_eq_nearest_integer
-- name    : DeletionCode.CircleHash.norm_coe_eq_nearest_integer
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:28:37.3444+00:00
-- url     : https://prove2.me/theorems/6980e0d9-648b-4f30-9855-1ebc07dd4ae0
-- title:
--   Circle Hash: norm coe eq nearest integer
-- statement:
--   This is the paper's distance to the nearest integer, attained at round r.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CircleHash.lean#L86-L88
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CircleHash.lean#L86-L88

import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Algebra.Order.Floor.Ring
import Definitions.Def_DeletionCode_CircleHash
set_option autoImplicit true
open DeletionCode DeletionCode.CircleHash
open scoped BigOperators

theorem DeletionCode.CircleHash.norm_coe_eq_nearest_integer (r : ℝ) :
    ‖(r : UnitAddCircle)‖ = |r - (round r : ℝ)| := by sorry
