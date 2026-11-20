-- Prove2me | Theorems.Thm_DeletionCode_UniqueRuns_no_constant_succ_window
-- name    : DeletionCode.UniqueRuns.no_constant_succ_window
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:16:29.681075+00:00
-- url     : https://prove2.me/theorems/732d4669-ddd2-412a-adbb-e69e8a05dfba
-- title:
--   Unique Runs: no constant succ window
-- statement:
--   In particular there is no in-bounds constant window of length k+1.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/UniqueRuns.lean#L33-L38
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/UniqueRuns.lean#L33-L38

import Definitions.Def_DeletionCode_Windows
import Definitions.Def_DeletionCode_UniqueRuns
set_option autoImplicit true
open DeletionCode DeletionCode.UniqueRuns
open Windows

theorem DeletionCode.UniqueRuns.no_constant_succ_window (k n : ℕ) (x : Letters) (hx : KUnique x n k)
    (a : ℕ) (bit : Bool) (hbound : a + (k + 1) ≤ n) :
    ¬ ConstantOn x a (k + 1) bit := by sorry
