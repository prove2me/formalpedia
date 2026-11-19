-- Prove2me | Theorems.Thm_DeletionCode_Windows_three_windows_overlap
-- name    : DeletionCode.Windows.three_windows_overlap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T04:57:58.937412+00:00
-- url     : https://prove2.me/theorems/959cdc22-7f7b-499c-89fa-7bc2da49978d
-- title:
--   Windows: three windows overlap
-- statement:
--   The Windows construction uses the three windows overlap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/Windows.lean#L41-L43
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/Windows.lean#L41-L43

import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_Windows
set_option autoImplicit true
open DeletionCode DeletionCode.Windows

theorem DeletionCode.Windows.three_windows_overlap (k D : ℕ) (hD : D < 3 * (k + 1)) :
    D / 2 + k ≤ 3 * (k + 1) ∧
    (D - D / 2) + k ≤ 3 * (k + 1) := by sorry
