-- Prove2me | Theorems.Thm_DeletionCode_GeneratingCount_generatingData_card_bound
-- name    : DeletionCode.GeneratingCount.generatingData_card_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:08:14.627816+00:00
-- url     : https://prove2.me/theorems/4f0c00c8-9774-4bb2-82de-43ba97a4a5ec
-- title:
--   Generating Count: generating Data card bound
-- statement:
--   The complete class of generating finite path data obeys the description bound.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/GeneratingCount.lean#L96-L104
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/GeneratingCount.lean#L96-L104

import Definitions.Def_DeletionCode_RecordSerialization
import Mathlib.SetTheory.Cardinal.Finite
import Definitions.Def_DeletionCode_GeneratingCount
set_option autoImplicit true
open DeletionCode DeletionCode.GeneratingCount
open Windows HeaderRecovery GeneratingModel GeneratingRecovery RecordSerialization DescriptionCount

theorem DeletionCode.GeneratingCount.generatingData_card_bound (x : Letters) (n k ν c : ℕ)
    (hν : 1 ≤ ν) (hx : KUnique x n k) :
    Nat.card {data : RecoveredData ν // GeneratingData x n k ν c data} ≤
      n ^ c * (fieldBound (windowLength k) ν) ^ (50 * ν) := by sorry
