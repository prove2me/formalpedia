-- Prove2me | Theorems.Thm_DeletionCode_GeneratingCount_encodeGeneratingData_injective
-- name    : DeletionCode.GeneratingCount.encodeGeneratingData_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:06:46.27118+00:00
-- url     : https://prove2.me/theorems/a8e1eb93-3b0b-4353-b286-577e69507a91
-- title:
--   Generating Count: encode Generating Data injective
-- statement:
--   The Generating Count construction uses the encode Generating Data injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/GeneratingCount.lean#L43-L50
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/GeneratingCount.lean#L43-L50

import Definitions.Def_DeletionCode_RecordSerialization
import Mathlib.SetTheory.Cardinal.Finite
import Definitions.Def_DeletionCode_GeneratingCount
set_option autoImplicit true
open DeletionCode DeletionCode.GeneratingCount
open Windows HeaderRecovery GeneratingModel GeneratingRecovery RecordSerialization DescriptionCount

theorem DeletionCode.GeneratingCount.encodeGeneratingData_injective (x : Letters) (n k ν c : ℕ)
    (hν : 1 ≤ ν) (hx : KUnique x n k) :
    Function.Injective (encodeGeneratingData x n k ν c hν hx) := by sorry
