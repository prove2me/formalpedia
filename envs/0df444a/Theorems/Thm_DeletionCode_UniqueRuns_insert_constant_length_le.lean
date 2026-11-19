-- Prove2me | Theorems.Thm_DeletionCode_UniqueRuns_insert_constant_length_le
-- name    : DeletionCode.UniqueRuns.insert_constant_length_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:30:49.133821+00:00
-- url     : https://prove2.me/theorems/16af65c6-dad5-4f8a-bd86-2b751030db5e
-- title:
--   Unique Runs: insert constant length le
-- statement:
--   A constant substring after a valid insertion has length at most k+1.
--   The inserted bit and the constant substring's bit need not be supplied as equal.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/UniqueRuns.lean#L42-L73
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/UniqueRuns.lean#L42-L73

import Definitions.Def_DeletionCode_Windows
import Definitions.Def_DeletionCode_UniqueRuns
set_option autoImplicit true
open DeletionCode DeletionCode.UniqueRuns
open Windows

theorem DeletionCode.UniqueRuns.insert_constant_length_le (k n : ℕ) (x : Letters) (hx : KUnique x n k)
    (pos : ℕ) (insertedBit : Bool) (hpos : pos ≤ n)
    (a len : ℕ) (bit : Bool) (hbound : a + len ≤ n + 1)
    (hconstant : ConstantOn (insertAt x pos insertedBit) a len bit) : len ≤ k + 1 := by sorry
