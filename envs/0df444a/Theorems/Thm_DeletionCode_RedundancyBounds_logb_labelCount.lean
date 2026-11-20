-- Prove2me | Theorems.Thm_DeletionCode_RedundancyBounds_logb_labelCount
-- name    : DeletionCode.RedundancyBounds.logb_labelCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:50:04.591494+00:00
-- url     : https://prove2.me/theorems/8c2ccf10-93b9-4cea-be0b-7d6e16ce1748
-- title:
--   Redundancy Bounds: logb label Count
-- statement:
--   The Redundancy Bounds construction uses the logb label Count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RedundancyBounds.lean#L60-L73
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RedundancyBounds.lean#L60-L73

import Definitions.Def_DeletionCode_PaperParameters
import Definitions.Def_DeletionCode_WitnessCost
import Definitions.Def_DeletionCode_RedundancyBounds
set_option autoImplicit true
open DeletionCode DeletionCode.RedundancyBounds
open HeaderRecovery

theorem DeletionCode.RedundancyBounds.logb_labelCount (t n : ℕ) (hn : 1 ≤ n) :
    Real.logb 2 (labelCount t n : ℝ) =
      3 + ((2 * t - 1 : ℕ) : ℝ) * Real.logb 2 (n : ℝ) +
        (WitnessCost.exponent t : ℝ) * Real.logb 2 (PaperParameters.L n : ℝ) := by sorry
