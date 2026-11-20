-- Prove2me | Theorems.Thm_DeletionCode_Windows_delete_insert
-- name    : DeletionCode.Windows.delete_insert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T04:57:58.203362+00:00
-- url     : https://prove2.me/theorems/7b7f3814-faab-43bf-a8a0-b225b86bf697
-- title:
--   Windows: delete insert
-- statement:
--   The Windows construction uses the delete insert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/Windows.lean#L65-L72
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/Windows.lean#L65-L72

import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_Windows
set_option autoImplicit true
open DeletionCode DeletionCode.Windows

theorem DeletionCode.Windows.delete_insert (p : Letters) (ell : ℕ) (d : Bool) :
    deleteAt (insertAt p ell d) ell = p := by sorry
