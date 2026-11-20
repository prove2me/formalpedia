-- Prove2me | Theorems.Thm_DeletionCode_CircleHash_equal_labels_small_representative
-- name    : DeletionCode.CircleHash.equal_labels_small_representative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:16:18.440627+00:00
-- url     : https://prove2.me/theorems/b9ceb008-7253-4a30-827d-5c2a79ef7117
-- title:
--   Circle Hash: equal labels small representative
-- statement:
--   The circle difference has a real representative in the required open interval.
--   This does not incorrectly require its [0,1) representative to be near zero.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CircleHash.lean#L64-L70
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CircleHash.lean#L64-L70

import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Algebra.Order.Floor.Ring
import Definitions.Def_DeletionCode_CircleHash
set_option autoImplicit true
open DeletionCode DeletionCode.CircleHash
open scoped BigOperators

theorem DeletionCode.CircleHash.equal_labels_small_representative (Q : ℕ) (hQ : 0 < Q)
    (a b : UnitAddCircle) (hlabel : label Q a = label Q b) :
    ∃ r : ℝ, (r : UnitAddCircle) = b - a ∧
      -(1 / (Q : ℝ)) < r ∧ r < 1 / (Q : ℝ) := by sorry
