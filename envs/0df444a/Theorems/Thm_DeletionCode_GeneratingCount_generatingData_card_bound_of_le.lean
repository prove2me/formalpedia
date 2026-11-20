-- Prove2me | Theorems.Thm_DeletionCode_GeneratingCount_generatingData_card_bound_of_le
-- name    : DeletionCode.GeneratingCount.generatingData_card_bound_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:07:36.781789+00:00
-- url     : https://prove2.me/theorems/3084262f-14aa-46ef-9afd-4f1dd8af956c
-- title:
--   Generating Count: generating Data card bound of le
-- statement:
--   The Generating Count construction uses the generating Data card bound of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/GeneratingCount.lean#L88-L93
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/GeneratingCount.lean#L88-L93

import Definitions.Def_DeletionCode_RecordSerialization
import Mathlib.SetTheory.Cardinal.Finite
import Definitions.Def_DeletionCode_GeneratingCount
set_option autoImplicit true
open DeletionCode DeletionCode.GeneratingCount
open Windows HeaderRecovery GeneratingModel GeneratingRecovery RecordSerialization DescriptionCount

theorem DeletionCode.GeneratingCount.generatingData_card_bound_of_le (x : Letters) (n k ν c : ℕ)
    (hν : 1 ≤ ν) (hx : KUnique x n k) (hc : c ≤ ν) :
    Nat.card {data : RecoveredData ν // GeneratingData x n k ν c data} ≤
      n ^ c * (fieldBound (windowLength k) ν) ^ (50 * ν) := by sorry
