-- Prove2me | Theorems.Thm_DeletionCode_TwoEditWindows_exists_clean_block_among_three
-- name    : DeletionCode.TwoEditWindows.exists_clean_block_among_three
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:28:55.175956+00:00
-- url     : https://prove2.me/theorems/a5760d4b-40cb-452a-8c88-1758c90ac026
-- title:
--   Two Edit Windows: exists clean block among three
-- statement:
--   Three separated candidate blocks suffice for any two edit positions.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TwoEditWindows.lean#L30-L57
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TwoEditWindows.lean#L30-L57

import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_TwoEditWindows
set_option autoImplicit true
open DeletionCode DeletionCode.TwoEditWindows

theorem DeletionCode.TwoEditWindows.exists_clean_block_among_three (k a b p q : ℕ) :
    ∃ s : ℕ, (s = 0 ∨ s = k + 1 ∨ s = 2 * (k + 1)) ∧
      s + k ≤ 3 * k + 2 ∧
      (a + s + k ≤ p ∨ p < a + s) ∧
      (b + s + k ≤ q ∨ q < b + s) := by sorry
