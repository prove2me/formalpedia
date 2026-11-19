-- Prove2me | Theorems.Thm_DeletionCode_RecordSerialization_serialized_generating_coverage
-- name    : DeletionCode.RecordSerialization.serialized_generating_coverage
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:18:04.297482+00:00
-- url     : https://prove2.me/theorems/c37b21e8-d2e5-4e02-8228-84c20cdf192b
-- title:
--   Record Serialization: serialized generating coverage
-- statement:
--   Every generating edited family has a description in the counted finite format.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RecordSerialization.lean#L100-L119
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RecordSerialization.lean#L100-L119

import Definitions.Def_DeletionCode_RecordBounds
import Definitions.Def_DeletionCode_RecordPacking
import Definitions.Def_DeletionCode_RecordSerialization
set_option autoImplicit true
open DeletionCode DeletionCode.RecordSerialization
open Windows HeaderRecovery ConcreteDecoder DescriptionCount RecordCodec
open RecordPacking GeneratingModel

theorem DeletionCode.RecordSerialization.serialized_generating_coverage {ν k : ℕ} (E : EditedFamily (Fin ν) k)
    (x : Letters) (n c : ℕ) (hν : 1 ≤ ν) (hx : KUnique x n k)
    (hg : E.family.Generating x n (windowLength k))
    (hc : Fintype.card (SupportComponents.GraphComponents E.family (windowLength k)) = c) :
    ∃ description : Description n (windowLength k) ν c,
      decodeDescription x n k ν c hν description = some (dataOfFamily E) := by sorry
