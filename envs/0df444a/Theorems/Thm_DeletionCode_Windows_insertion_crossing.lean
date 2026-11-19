-- Prove2me | Theorems.Thm_DeletionCode_Windows_insertion_crossing
-- name    : DeletionCode.Windows.insertion_crossing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T04:58:26.817758+00:00
-- url     : https://prove2.me/theorems/b3732f24-cd4f-4e9f-b28b-488e2030c22c
-- title:
--   Windows: insertion crossing
-- statement:
--   The Windows construction uses the insertion crossing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/Windows.lean#L137-L153
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/Windows.lean#L137-L153

import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_Windows
set_option autoImplicit true
open DeletionCode DeletionCode.Windows

theorem DeletionCode.Windows.insertion_crossing (p : Letters) (ell s k : ℕ) (d : Bool)
    (hs : s ≤ ell) :
    ∀ i, i < k → insertAt p ell d (s + i) =
      insertionSeed (ell - s) d (fun j => p (s + j)) i := by sorry
