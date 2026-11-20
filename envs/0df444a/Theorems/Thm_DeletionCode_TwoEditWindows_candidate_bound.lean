-- Prove2me | Theorems.Thm_DeletionCode_TwoEditWindows_candidate_bound
-- name    : DeletionCode.TwoEditWindows.candidate_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:16:22.970155+00:00
-- url     : https://prove2.me/theorems/ff353fb9-5c2b-41a3-9ad9-2e7eb3e67055
-- title:
--   Two Edit Windows: candidate bound
-- statement:
--   The candidate offsets all fit, including the final block's right endpoint.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TwoEditWindows.lean#L25-L27
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TwoEditWindows.lean#L25-L27

import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_TwoEditWindows
set_option autoImplicit true
open DeletionCode DeletionCode.TwoEditWindows

theorem DeletionCode.TwoEditWindows.candidate_bound {k s : ℕ}
    (hs : s = 0 ∨ s = k + 1 ∨ s = 2 * (k + 1)) : s + k ≤ 3 * k + 2 := by sorry
