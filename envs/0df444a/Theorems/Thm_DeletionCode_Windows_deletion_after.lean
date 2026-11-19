-- Prove2me | Theorems.Thm_DeletionCode_Windows_deletion_after
-- name    : DeletionCode.Windows.deletion_after
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T04:58:15.709877+00:00
-- url     : https://prove2.me/theorems/728e986d-abd0-4ab4-947a-ab15a24002d8
-- title:
--   Windows: deletion after
-- statement:
--   The Windows construction uses the deletion after property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/Windows.lean#L92-L97
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/Windows.lean#L92-L97

import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_Windows
set_option autoImplicit true
open DeletionCode DeletionCode.Windows

theorem DeletionCode.Windows.deletion_after (p : Letters) (ell s k : ℕ)
    (h : ell < s) : Agree (deleteAt p ell) (s - 1) p s k := by sorry
