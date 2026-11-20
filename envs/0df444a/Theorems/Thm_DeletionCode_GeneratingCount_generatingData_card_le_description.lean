-- Prove2me | Theorems.Thm_DeletionCode_GeneratingCount_generatingData_card_le_description
-- name    : DeletionCode.GeneratingCount.generatingData_card_le_description
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:07:24.877967+00:00
-- url     : https://prove2.me/theorems/80da4c35-ee81-44b6-8d2b-bc0fcfcc0d2c
-- title:
--   Generating Count: generating Data card le description
-- statement:
--   The Generating Count construction uses the generating Data card le description property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/GeneratingCount.lean#L59-L65
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/GeneratingCount.lean#L59-L65

import Definitions.Def_DeletionCode_RecordSerialization
import Mathlib.SetTheory.Cardinal.Finite
import Definitions.Def_DeletionCode_GeneratingCount
set_option autoImplicit true
open DeletionCode DeletionCode.GeneratingCount
open Windows HeaderRecovery GeneratingModel GeneratingRecovery RecordSerialization DescriptionCount

theorem DeletionCode.GeneratingCount.generatingData_card_le_description (x : Letters) (n k ν c : ℕ)
    (hν : 1 ≤ ν) (hx : KUnique x n k) :
    Nat.card {data : RecoveredData ν // GeneratingData x n k ν c data} ≤
      Fintype.card (Description n (windowLength k) ν c) := by sorry
