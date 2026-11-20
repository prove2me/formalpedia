-- Prove2me | Theorems.Thm_DeletionCode_EditAlignment_Script_surviving_subsequence
-- name    : DeletionCode.EditAlignment.Script.surviving_subsequence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:04:17.9012+00:00
-- url     : https://prove2.me/theorems/2437ab63-f0ee-464d-b783-c5f23d127d54
-- title:
--   Script: surviving subsequence
-- statement:
--   At most d original letters are lost during a script with d deletions.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/EditAlignment.lean#L75-L87
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/EditAlignment.lean#L75-L87

import Mathlib.Data.List.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_EditAlignment
set_option autoImplicit true
open DeletionCode DeletionCode.EditAlignment

theorem DeletionCode.EditAlignment.Script.surviving_subsequence {y z : Word} {d i : ℕ} (h : Script y z d i) :
    ∃ w : Word, w.Sublist y ∧ w.Sublist z ∧ y.length ≤ w.length + d := by sorry
