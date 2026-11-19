-- Prove2me | Theorems.Thm_DeletionCode_PaperParameters_logb_L_le_six_logb_logb
-- name    : DeletionCode.PaperParameters.logb_L_le_six_logb_logb
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:37:51.995063+00:00
-- url     : https://prove2.me/theorems/69b101de-963a-45a3-ab0c-1d879390b6f2
-- title:
--   Paper Parameters: logb L le six logb logb
-- statement:
--   The logarithm of the window length is bounded by six times log-log.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/PaperParameters.lean#L124-L137
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/PaperParameters.lean#L124-L137

import Definitions.Def_DeletionCode_UniqueWordParameters
import Definitions.Def_DeletionCode_HeaderRecovery
import Mathlib.Analysis.Asymptotics.Defs
import Definitions.Def_DeletionCode_PaperParameters
set_option autoImplicit true
open DeletionCode DeletionCode.PaperParameters
open Filter Asymptotics
open scoped Topology

theorem DeletionCode.PaperParameters.logb_L_le_six_logb_logb (n : ℕ) (hn : 4 ≤ n) :
    Real.logb 2 (L n : ℝ) ≤ 6 * Real.logb 2 (Real.logb 2 (n : ℝ)) := by sorry
