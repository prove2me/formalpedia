-- Prove2me | Theorems.Thm_DeletionCode_EditAlignment_sublist_survives_delete
-- name    : DeletionCode.EditAlignment.sublist_survives_delete
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:04:07.703394+00:00
-- url     : https://prove2.me/theorems/8e6f3975-cde2-4f67-b6d5-0f6558f6c1ea
-- title:
--   Edit Alignment: sublist survives delete
-- statement:
--   Deleting one target position loses at most one letter of any surviving subsequence.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/EditAlignment.lean#L60-L72
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/EditAlignment.lean#L60-L72

import Mathlib.Data.List.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_EditAlignment
set_option autoImplicit true
open DeletionCode DeletionCode.EditAlignment

theorem DeletionCode.EditAlignment.sublist_survives_delete (w pre suffix : Word) (bit : Bool)
    (h : w.Sublist (pre ++ bit :: suffix)) :
    ∃ v : Word, v.Sublist w ∧ v.Sublist (pre ++ suffix) ∧ w.length ≤ v.length + 1 := by sorry
