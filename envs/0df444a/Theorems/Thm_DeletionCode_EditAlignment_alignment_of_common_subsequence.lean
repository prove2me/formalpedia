-- Prove2me | Theorems.Thm_DeletionCode_EditAlignment_alignment_of_common_subsequence
-- name    : DeletionCode.EditAlignment.alignment_of_common_subsequence
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:04:17.032802+00:00
-- url     : https://prove2.me/theorems/318ad6da-d347-432b-bd45-073a897d02da
-- title:
--   Edit Alignment: alignment of common subsequence
-- statement:
--   Match a common subsequence and put every remaining letter in its own edit column.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/EditAlignment.lean#L95-L121
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/EditAlignment.lean#L95-L121

import Mathlib.Data.List.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_EditAlignment
set_option autoImplicit true
open DeletionCode DeletionCode.EditAlignment

theorem DeletionCode.EditAlignment.alignment_of_common_subsequence {w y z : Word}
    (hy : w.Sublist y) (hz : w.Sublist z) :
    Alignment y z (y.length - w.length) (z.length - w.length) := by sorry
