-- Prove2me | Theorems.Thm_DeletionCode_WitnessCost_length_le_two_pow_window
-- name    : DeletionCode.WitnessCost.length_le_two_pow_window
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:46:26.579879+00:00
-- url     : https://prove2.me/theorems/1413f48e-40b1-4469-829a-af10fc9bfa5e
-- title:
--   Witness Cost: length le two pow window
-- statement:
--   The paper's actual ceiling-logarithm choice bounds n by 2^L.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WitnessCost.lean#L74-L79
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WitnessCost.lean#L74-L79

import Definitions.Def_DeletionCode_CountExponent
import Definitions.Def_DeletionCode_UniqueWordParameters
import Definitions.Def_DeletionCode_WitnessCost
set_option autoImplicit true
open DeletionCode DeletionCode.WitnessCost
open HeaderRecovery UniqueWordParameters

theorem DeletionCode.WitnessCost.length_le_two_pow_window (n : ℕ) :
    n ≤ 2 ^ windowLength (uniquenessLength n) := by sorry
