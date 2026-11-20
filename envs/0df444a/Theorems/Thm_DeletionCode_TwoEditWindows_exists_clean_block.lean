-- Prove2me | Theorems.Thm_DeletionCode_TwoEditWindows_exists_clean_block
-- name    : DeletionCode.TwoEditWindows.exists_clean_block
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:28:57.938201+00:00
-- url     : https://prove2.me/theorems/924290f7-3ded-4684-ad0d-0dfa65e7e804
-- title:
--   Two Edit Windows: exists clean block
-- statement:
--   Arithmetic interface for a common unedited subwindow of two words.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TwoEditWindows.lean#L60-L65
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TwoEditWindows.lean#L60-L65

import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_TwoEditWindows
set_option autoImplicit true
open DeletionCode DeletionCode.TwoEditWindows

theorem DeletionCode.TwoEditWindows.exists_clean_block (k a b p q : ℕ) :
    ∃ s : ℕ, s + k ≤ 3 * k + 2 ∧
      (a + s + k ≤ p ∨ p < a + s) ∧
      (b + s + k ≤ q ∨ q < b + s) := by sorry
