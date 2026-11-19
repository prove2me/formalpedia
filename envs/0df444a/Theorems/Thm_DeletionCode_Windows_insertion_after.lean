-- Prove2me | Theorems.Thm_DeletionCode_Windows_insertion_after
-- name    : DeletionCode.Windows.insertion_after
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T04:58:26.189771+00:00
-- url     : https://prove2.me/theorems/a355d9d7-9d2f-42e8-9f84-b4372150dc52
-- title:
--   Windows: insertion after
-- statement:
--   The Windows construction uses the insertion after property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/Windows.lean#L129-L135
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/Windows.lean#L129-L135

import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_Windows
set_option autoImplicit true
open DeletionCode DeletionCode.Windows

theorem DeletionCode.Windows.insertion_after (p : Letters) (ell s k : ℕ) (d : Bool)
    (h : ell ≤ s) : Agree (insertAt p ell d) (s + 1) p s k := by sorry
