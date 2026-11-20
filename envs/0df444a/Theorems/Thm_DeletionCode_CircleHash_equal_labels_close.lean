-- Prove2me | Theorems.Thm_DeletionCode_CircleHash_equal_labels_close
-- name    : DeletionCode.CircleHash.equal_labels_close
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:28:30.768645+00:00
-- url     : https://prove2.me/theorems/a689770d-6514-4c48-b698-af7ffffa9594
-- title:
--   Circle Hash: equal labels close
-- statement:
--   The actual quotient norm is no larger than the short representative difference.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CircleHash.lean#L73-L83
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CircleHash.lean#L73-L83

import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Algebra.Order.Floor.Ring
import Definitions.Def_DeletionCode_CircleHash
set_option autoImplicit true
open DeletionCode DeletionCode.CircleHash
open scoped BigOperators

theorem DeletionCode.CircleHash.equal_labels_close (Q : ℕ) (hQ : 0 < Q)
    (a b : UnitAddCircle) (hlabel : label Q a = label Q b) :
    ‖b - a‖ < 1 / (Q : ℝ) := by sorry
