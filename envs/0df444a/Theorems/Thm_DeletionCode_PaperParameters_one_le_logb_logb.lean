-- Prove2me | Theorems.Thm_DeletionCode_PaperParameters_one_le_logb_logb
-- name    : DeletionCode.PaperParameters.one_le_logb_logb
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:30:37.41162+00:00
-- url     : https://prove2.me/theorems/a1a5da76-25a1-4d69-9138-f410e30eb6be
-- title:
--   Paper Parameters: one le logb logb
-- statement:
--   The Paper Parameters construction uses the one le logb logb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/PaperParameters.lean#L117-L121
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/PaperParameters.lean#L117-L121

import Definitions.Def_DeletionCode_UniqueWordParameters
import Definitions.Def_DeletionCode_HeaderRecovery
import Mathlib.Analysis.Asymptotics.Defs
import Definitions.Def_DeletionCode_PaperParameters
set_option autoImplicit true
open DeletionCode DeletionCode.PaperParameters
open Filter Asymptotics
open scoped Topology

theorem DeletionCode.PaperParameters.one_le_logb_logb (n : ℕ) (hn : 4 ≤ n) :
    1 ≤ Real.logb 2 (Real.logb 2 (n : ℝ)) := by sorry
