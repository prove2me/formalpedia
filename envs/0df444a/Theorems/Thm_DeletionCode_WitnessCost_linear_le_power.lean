-- Prove2me | Theorems.Thm_DeletionCode_WitnessCost_linear_le_power
-- name    : DeletionCode.WitnessCost.linear_le_power
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:45:14.622181+00:00
-- url     : https://prove2.me/theorems/8c63a643-0287-47cb-811b-1e441cc32f48
-- title:
--   Witness Cost: linear le power
-- statement:
--   The elementary Bernoulli bound, including exponent zero.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WitnessCost.lean#L22-L31
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WitnessCost.lean#L22-L31

import Definitions.Def_DeletionCode_CountExponent
import Definitions.Def_DeletionCode_UniqueWordParameters
import Definitions.Def_DeletionCode_WitnessCost
set_option autoImplicit true
open DeletionCode DeletionCode.WitnessCost
open HeaderRecovery UniqueWordParameters

theorem DeletionCode.WitnessCost.linear_le_power (c R : ℕ) : c * R + 1 ≤ (c + 1) ^ R := by sorry
