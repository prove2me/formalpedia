-- Prove2me | Theorems.Thm_DeletionCode_PaperParameters_le_two_pow_of_L_lt
-- name    : DeletionCode.PaperParameters.le_two_pow_of_L_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:49:26.153046+00:00
-- url     : https://prove2.me/theorems/b934a5da-beda-4faf-a668-1c12e11396b8
-- title:
--   Paper Parameters: le two pow of L lt
-- statement:
--   This discharges the extra-component arithmetic premise in WitnessCounting.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/PaperParameters.lean#L77-L80
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/PaperParameters.lean#L77-L80

import Definitions.Def_DeletionCode_UniqueWordParameters
import Definitions.Def_DeletionCode_HeaderRecovery
import Mathlib.Analysis.Asymptotics.Defs
import Definitions.Def_DeletionCode_PaperParameters
set_option autoImplicit true
open DeletionCode DeletionCode.PaperParameters
open Filter Asymptotics
open scoped Topology

theorem DeletionCode.PaperParameters.le_two_pow_of_L_lt (n R : ℕ) (hR : L n < R) : n ≤ 2 ^ R := by sorry
