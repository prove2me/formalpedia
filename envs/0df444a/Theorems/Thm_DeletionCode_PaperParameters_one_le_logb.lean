-- Prove2me | Theorems.Thm_DeletionCode_PaperParameters_one_le_logb
-- name    : DeletionCode.PaperParameters.one_le_logb
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:30:15.895221+00:00
-- url     : https://prove2.me/theorems/5d874559-01b0-443b-bac8-5217af54af43
-- title:
--   Paper Parameters: one le logb
-- statement:
--   The Paper Parameters construction uses the one le logb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/PaperParameters.lean#L82-L85
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/PaperParameters.lean#L82-L85

import Definitions.Def_DeletionCode_UniqueWordParameters
import Definitions.Def_DeletionCode_HeaderRecovery
import Mathlib.Analysis.Asymptotics.Defs
import Definitions.Def_DeletionCode_PaperParameters
set_option autoImplicit true
open DeletionCode DeletionCode.PaperParameters
open Filter Asymptotics
open scoped Topology

theorem DeletionCode.PaperParameters.one_le_logb (n : ℕ) (hn : 2 ≤ n) : 1 ≤ Real.logb 2 (n : ℝ) := by sorry
