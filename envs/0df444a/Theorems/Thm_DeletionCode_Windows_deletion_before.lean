-- Prove2me | Theorems.Thm_DeletionCode_Windows_deletion_before
-- name    : DeletionCode.Windows.deletion_before
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T04:58:13.213762+00:00
-- url     : https://prove2.me/theorems/708af61a-bbba-43c5-acd9-a166b4b272ca
-- title:
--   Windows: deletion before
-- statement:
--   The Windows construction uses the deletion before property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/Windows.lean#L86-L90
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/Windows.lean#L86-L90

import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_Windows
set_option autoImplicit true
open DeletionCode DeletionCode.Windows

theorem DeletionCode.Windows.deletion_before (p : Letters) (ell s k : ℕ)
    (h : s + k ≤ ell) : Agree (deleteAt p ell) s p s k := by sorry
