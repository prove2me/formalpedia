-- Prove2me | Theorems.Thm_DeletionCode_GeneratingCount_editedFamily_component_count_le
-- name    : DeletionCode.GeneratingCount.editedFamily_component_count_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:07:18.290836+00:00
-- url     : https://prove2.me/theorems/f1a88ec1-b5a5-4cc3-ade7-d4b9bdc7e95d
-- title:
--   Generating Count: edited Family component count le
-- statement:
--   There cannot be more supported graph components than indexed bubbles.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/GeneratingCount.lean#L68-L80
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/GeneratingCount.lean#L68-L80

import Definitions.Def_DeletionCode_RecordSerialization
import Mathlib.SetTheory.Cardinal.Finite
import Definitions.Def_DeletionCode_GeneratingCount
set_option autoImplicit true
open DeletionCode DeletionCode.GeneratingCount
open Windows HeaderRecovery GeneratingModel GeneratingRecovery RecordSerialization DescriptionCount

theorem DeletionCode.GeneratingCount.editedFamily_component_count_le {ν k : ℕ} (E : EditedFamily (Fin ν) k) :
    Fintype.card (SupportComponents.GraphComponents E.family (windowLength k)) ≤ ν := by sorry
