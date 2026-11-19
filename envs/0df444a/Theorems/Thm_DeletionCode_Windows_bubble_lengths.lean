-- Prove2me | Theorems.Thm_DeletionCode_Windows_bubble_lengths
-- name    : DeletionCode.Windows.bubble_lengths
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T04:57:56.599822+00:00
-- url     : https://prove2.me/theorems/1f1673be-f658-4693-9d0a-821e5a2c61d6
-- title:
--   Windows: bubble lengths
-- statement:
--   The Windows construction uses the bubble lengths property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/Windows.lean#L45-L50
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/Windows.lean#L45-L50

import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_Windows
set_option autoImplicit true
open DeletionCode DeletionCode.Windows

theorem DeletionCode.Windows.bubble_lengths (k ρ : ℕ) (hρ0 : 1 ≤ ρ) (hρ1 : ρ ≤ k + 1) :
    let L := 3 * (k + 1)
    L - ρ < L ∧ L - ρ - 1 < L ∧
    k + 1 < 2 * L - ρ - 1 ∧ (L - 1) + k < 2 * L - ρ := by sorry
