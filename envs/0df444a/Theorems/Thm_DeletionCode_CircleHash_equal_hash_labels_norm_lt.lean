-- Prove2me | Theorems.Thm_DeletionCode_CircleHash_equal_hash_labels_norm_lt
-- name    : DeletionCode.CircleHash.equal_hash_labels_norm_lt
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:28:46.065347+00:00
-- url     : https://prove2.me/theorems/0c4f9ee2-9ac5-4b76-a16a-b244b86a521a
-- title:
--   Circle Hash: equal hash labels norm lt
-- statement:
--   Equal hash labels force the actual spectrum difference to pass the test.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CircleHash.lean#L129-L134
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CircleHash.lean#L129-L134

import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Algebra.Order.Floor.Ring
import Definitions.Def_DeletionCode_CircleHash
set_option autoImplicit true
open DeletionCode DeletionCode.CircleHash
open scoped BigOperators

theorem DeletionCode.CircleHash.equal_hash_labels_norm_lt {V : Type*} [AddCommGroup V]
    (H : V →+ UnitAddCircle) (Q : ℕ) (hQ : 2 ≤ Q) (p p' : V)
    (hlabel : label Q (H p) = label Q (H p')) :
    ‖H (p' - p)‖ < 1 / (Q : ℝ) := by sorry
