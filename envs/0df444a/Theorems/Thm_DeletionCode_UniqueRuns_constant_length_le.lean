-- Prove2me | Theorems.Thm_DeletionCode_UniqueRuns_constant_length_le
-- name    : DeletionCode.UniqueRuns.constant_length_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:20:22.912622+00:00
-- url     : https://prove2.me/theorems/ea8a38ce-cc87-421c-b8eb-cb03f661493f
-- title:
--   Unique Runs: constant length le
-- statement:
--   Every in-bounds constant substring of a k-unique source has length at most k.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/UniqueRuns.lean#L18-L30
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/UniqueRuns.lean#L18-L30

import Definitions.Def_DeletionCode_Windows
import Definitions.Def_DeletionCode_UniqueRuns
set_option autoImplicit true
open DeletionCode DeletionCode.UniqueRuns
open Windows

theorem DeletionCode.UniqueRuns.constant_length_le (k n : ℕ) (x : Letters) (hx : KUnique x n k)
    (a len : ℕ) (bit : Bool) (hbound : a + len ≤ n)
    (hconstant : ConstantOn x a len bit) : len ≤ k := by sorry
