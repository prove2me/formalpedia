-- Prove2me | Theorems.Thm_DeletionCode_Windows_crossing_extension_in_bounds
-- name    : DeletionCode.Windows.crossing_extension_in_bounds
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T04:58:14.44551+00:00
-- url     : https://prove2.me/theorems/d71a3d97-0e07-4e74-bb8c-9661695ec9f0
-- title:
--   Windows: crossing extension in bounds
-- statement:
--   For the paper's parameters, a crossing seed has room to extend right.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/Windows.lean#L118-L121
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/Windows.lean#L118-L121

import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_Windows
set_option autoImplicit true
open DeletionCode DeletionCode.Windows

theorem DeletionCode.Windows.crossing_extension_in_bounds
    (k ρ s : ℕ) (hρ0 : 1 ≤ ρ) (hρ1 : ρ ≤ k + 1)
    (hs : s ≤ 3 * (k + 1) - 1) :
    s + k ≤ 2 * (3 * (k + 1)) - ρ - 1 := by sorry
