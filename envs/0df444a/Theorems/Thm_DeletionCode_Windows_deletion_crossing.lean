-- Prove2me | Theorems.Thm_DeletionCode_Windows_deletion_crossing
-- name    : DeletionCode.Windows.deletion_crossing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T04:58:12.021245+00:00
-- url     : https://prove2.me/theorems/4141b5d5-9dce-496c-bfc1-bd27a1b3a428
-- title:
--   Windows: deletion crossing
-- statement:
--   Crossing deletion: k-1 surviving letters and one right-extension bit.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/Windows.lean#L100-L115
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/Windows.lean#L100-L115

import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_Windows
set_option autoImplicit true
open DeletionCode DeletionCode.Windows

theorem DeletionCode.Windows.deletion_crossing (p : Letters) (ell s k : ℕ)
    (hs : s ≤ ell) (he : ell < s + k) :
    ∀ i, i < k → deleteAt p ell (s + i) =
      deletionSeed k (ell - s) (deleteAt p ell (s + k - 1))
        (fun j => p (s + j)) i := by sorry
