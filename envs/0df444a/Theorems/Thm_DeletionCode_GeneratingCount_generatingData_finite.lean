-- Prove2me | Theorems.Thm_DeletionCode_GeneratingCount_generatingData_finite
-- name    : DeletionCode.GeneratingCount.generatingData_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:07:05.5591+00:00
-- url     : https://prove2.me/theorems/e3473477-7032-4f71-9415-fea42f88902f
-- title:
--   Generating Count: generating Data finite
-- statement:
--   The entire class of generating finite data is finite, without a Fintype premise.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/GeneratingCount.lean#L53-L57
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/GeneratingCount.lean#L53-L57

import Definitions.Def_DeletionCode_RecordSerialization
import Mathlib.SetTheory.Cardinal.Finite
import Definitions.Def_DeletionCode_GeneratingCount
set_option autoImplicit true
open DeletionCode DeletionCode.GeneratingCount
open Windows HeaderRecovery GeneratingModel GeneratingRecovery RecordSerialization DescriptionCount

theorem DeletionCode.GeneratingCount.generatingData_finite (x : Letters) (n k ν c : ℕ)
    (hν : 1 ≤ ν) (hx : KUnique x n k) :
    Finite {data : RecoveredData ν // GeneratingData x n k ν c data} := by sorry
