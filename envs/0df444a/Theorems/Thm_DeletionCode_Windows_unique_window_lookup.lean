-- Prove2me | Theorems.Thm_DeletionCode_Windows_unique_window_lookup
-- name    : DeletionCode.Windows.unique_window_lookup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T04:57:57.117118+00:00
-- url     : https://prove2.me/theorems/bfe6ebb3-7638-4b89-8fe4-65812dbe0636
-- title:
--   Windows: unique window lookup
-- statement:
--   A known k-stretch at a fixed offset determines a window in x.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/Windows.lean#L21-L27
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/Windows.lean#L21-L27

import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_Windows
set_option autoImplicit true
open DeletionCode DeletionCode.Windows

theorem DeletionCode.Windows.unique_window_lookup
    (x : Letters) (n k L a b r : ℕ)
    (hx : KUnique x n k) (ha : a + L ≤ n) (hb : b + L ≤ n)
    (hr : r + k ≤ L) (h : Agree x (a + r) x (b + r) k) : a = b := by sorry
