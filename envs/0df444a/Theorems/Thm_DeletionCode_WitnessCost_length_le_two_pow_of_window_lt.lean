-- Prove2me | Theorems.Thm_DeletionCode_WitnessCost_length_le_two_pow_of_window_lt
-- name    : DeletionCode.WitnessCost.length_le_two_pow_of_window_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:17:17.496178+00:00
-- url     : https://prove2.me/theorems/adca1a68-1b6d-480f-b2eb-7bb26335aae0
-- title:
--   Witness Cost: length le two pow of window lt
-- statement:
--   In the large-witness case L < R, the extra factor n costs at most 2^R.
--   No asymptotic or logarithmic approximation is assumed. The result even
--   includes n = 0; positive n is the manuscript's intended application.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WitnessCost.lean#L84-L87
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WitnessCost.lean#L84-L87

import Definitions.Def_DeletionCode_CountExponent
import Definitions.Def_DeletionCode_UniqueWordParameters
import Definitions.Def_DeletionCode_WitnessCost
set_option autoImplicit true
open DeletionCode DeletionCode.WitnessCost
open HeaderRecovery UniqueWordParameters

theorem DeletionCode.WitnessCost.length_le_two_pow_of_window_lt (n R : ℕ)
    (hR : windowLength (uniquenessLength n) < R) : n ≤ 2 ^ R := by sorry
