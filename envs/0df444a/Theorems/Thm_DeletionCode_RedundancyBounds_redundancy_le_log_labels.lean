-- Prove2me | Theorems.Thm_DeletionCode_RedundancyBounds_redundancy_le_log_labels
-- name    : DeletionCode.RedundancyBounds.redundancy_le_log_labels
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:49:22.587301+00:00
-- url     : https://prove2.me/theorems/6e33692d-e001-4273-a737-03965e76a76f
-- title:
--   Redundancy Bounds: redundancy le log labels
-- statement:
--   The finite counting estimate gives redundancy at most log₂ Q + 3.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RedundancyBounds.lean#L36-L49
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RedundancyBounds.lean#L36-L49

import Definitions.Def_DeletionCode_PaperParameters
import Definitions.Def_DeletionCode_WitnessCost
import Definitions.Def_DeletionCode_RedundancyBounds
set_option autoImplicit true
open DeletionCode DeletionCode.RedundancyBounds
open HeaderRecovery

theorem DeletionCode.RedundancyBounds.redundancy_le_log_labels (n Q : ℕ) (C : Finset (Bits n))
    (hQ : 1 ≤ Q) (hcard : 2 ^ n ≤ 8 * Q * C.card) :
    redundancy n C ≤ Real.logb 2 (Q : ℝ) + 3 := by sorry
