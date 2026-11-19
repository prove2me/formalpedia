-- Prove2me | Theorems.Thm_DeletionCode_CircleHash_equal_scaled_floors_close
-- name    : DeletionCode.CircleHash.equal_scaled_floors_close
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:28:25.92886+00:00
-- url     : https://prove2.me/theorems/fcb4b491-50f0-4608-921a-bf51abbbbf12
-- title:
--   Circle Hash: equal scaled floors close
-- statement:
--   The strict upper endpoint of each half-open bin gives a strict difference bound.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CircleHash.lean#L48-L55
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CircleHash.lean#L48-L55

import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Algebra.Order.Floor.Ring
import Definitions.Def_DeletionCode_CircleHash
set_option autoImplicit true
open DeletionCode DeletionCode.CircleHash
open scoped BigOperators

theorem DeletionCode.CircleHash.equal_scaled_floors_close (Q : ℕ) (hQ : 0 < Q) (a b : ℝ)
    (hlabel : ⌊(Q : ℝ) * a⌋ = ⌊(Q : ℝ) * b⌋) :
    |b - a| < 1 / (Q : ℝ) := by sorry
