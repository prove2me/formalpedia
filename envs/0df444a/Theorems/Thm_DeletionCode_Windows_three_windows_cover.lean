-- Prove2me | Theorems.Thm_DeletionCode_Windows_three_windows_cover
-- name    : DeletionCode.Windows.three_windows_cover
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T04:57:57.509197+00:00
-- url     : https://prove2.me/theorems/6210641d-fa62-4c09-9d5f-5bf8faeaf77c
-- title:
--   Windows: three windows cover
-- statement:
--   The three selected windows contain every valid k-stretch.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/Windows.lean#L30-L39
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/Windows.lean#L30-L39

import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_Windows
set_option autoImplicit true
open DeletionCode DeletionCode.Windows

theorem DeletionCode.Windows.three_windows_cover
    (k D s : ℕ) (hD : D < 3 * (k + 1))
    (hs : s + k ≤ 3 * (k + 1) + D) :
    ∃ a : ℕ, (a = 0 ∨ a = D / 2 ∨ a = D) ∧
      a ≤ s ∧ s + k ≤ a + 3 * (k + 1) := by sorry
