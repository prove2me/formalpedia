-- Prove2me | Theorems.Thm_DeletionCode_CircleHash_label_range
-- name    : DeletionCode.CircleHash.label_range
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:29:46.133127+00:00
-- url     : https://prove2.me/theorems/d30bfce6-c6e5-4aaf-9b37-047c0648f1cc
-- title:
--   Circle Hash: label range
-- statement:
--   Thus the labels are exactly of the paper's type: integers from 0 through Q-1.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CircleHash.lean#L43-L45
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CircleHash.lean#L43-L45

import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Algebra.Order.Floor.Ring
import Definitions.Def_DeletionCode_CircleHash
set_option autoImplicit true
open DeletionCode DeletionCode.CircleHash
open scoped BigOperators

theorem DeletionCode.CircleHash.label_range (Q : ℕ) (hQ : 2 ≤ Q) (z : UnitAddCircle) :
    0 ≤ label Q z ∧ label Q z < (Q : ℤ) := by sorry
