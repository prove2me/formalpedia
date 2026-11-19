-- Prove2me | Theorems.Thm_DeletionCode_Windows_insert_delete
-- name    : DeletionCode.Windows.insert_delete
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T04:58:11.852877+00:00
-- url     : https://prove2.me/theorems/b35bdb81-52dc-4ee9-b0b2-cb3ddf382c66
-- title:
--   Windows: insert delete
-- statement:
--   The Windows construction uses the insert delete property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/Windows.lean#L74-L84
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/Windows.lean#L74-L84

import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_Windows
set_option autoImplicit true
open DeletionCode DeletionCode.Windows

theorem DeletionCode.Windows.insert_delete (p : Letters) (ell : ℕ) :
    insertAt (deleteAt p ell) ell (p ell) = p := by sorry
