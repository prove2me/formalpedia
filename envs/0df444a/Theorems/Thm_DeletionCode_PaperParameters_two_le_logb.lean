-- Prove2me | Theorems.Thm_DeletionCode_PaperParameters_two_le_logb
-- name    : DeletionCode.PaperParameters.two_le_logb
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:30:33.418324+00:00
-- url     : https://prove2.me/theorems/f9e49b86-dc00-4919-9269-24873763986f
-- title:
--   Paper Parameters: two le logb
-- statement:
--   The Paper Parameters construction uses the two le logb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/PaperParameters.lean#L87-L92
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/PaperParameters.lean#L87-L92

import Definitions.Def_DeletionCode_UniqueWordParameters
import Definitions.Def_DeletionCode_HeaderRecovery
import Mathlib.Analysis.Asymptotics.Defs
import Definitions.Def_DeletionCode_PaperParameters
set_option autoImplicit true
open DeletionCode DeletionCode.PaperParameters
open Filter Asymptotics
open scoped Topology

theorem DeletionCode.PaperParameters.two_le_logb (n : ℕ) (hn : 4 ≤ n) : 2 ≤ Real.logb 2 (n : ℝ) := by sorry
