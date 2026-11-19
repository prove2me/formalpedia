-- Prove2me | Theorems.Thm_DeletionCode_PaperParameters_L_le_twenty_one_logb
-- name    : DeletionCode.PaperParameters.L_le_twenty_one_logb
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:30:41.38369+00:00
-- url     : https://prove2.me/theorems/e254305c-2444-40b0-9c8b-d21036ce9e75
-- title:
--   Paper Parameters: L le twenty one logb
-- statement:
--   A pointwise logarithmic bound for the actual ceiling parameter.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/PaperParameters.lean#L95-L106
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/PaperParameters.lean#L95-L106

import Definitions.Def_DeletionCode_UniqueWordParameters
import Definitions.Def_DeletionCode_HeaderRecovery
import Mathlib.Analysis.Asymptotics.Defs
import Definitions.Def_DeletionCode_PaperParameters
set_option autoImplicit true
open DeletionCode DeletionCode.PaperParameters
open Filter Asymptotics
open scoped Topology

theorem DeletionCode.PaperParameters.L_le_twenty_one_logb (n : ℕ) (hn : 2 ≤ n) :
    (L n : ℝ) ≤ 21 * Real.logb 2 (n : ℝ) := by sorry
