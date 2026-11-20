-- Prove2me | Theorems.Thm_DeletionCode_ExceptionalPartnerCount_bad_record_of_not_separated
-- name    : DeletionCode.ExceptionalPartnerCount.bad_record_of_not_separated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:56:27.011241+00:00
-- url     : https://prove2.me/theorems/346439e6-1c93-44d1-8b11-8b2295c3ce38
-- title:
--   Exceptional Partner Count: bad record of not separated
-- statement:
--   Failure of actual matched-column separation forces one of the close-anchor
--   conditions on any faithful finite record. Repeated anchors retain distinct indices.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ExceptionalPartnerCount.lean#L73-L106
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ExceptionalPartnerCount.lean#L73-L106

import Definitions.Def_DeletionCode_AnchorRecords
import Definitions.Def_DeletionCode_TaggedAnchorCount
import Definitions.Def_DeletionCode_ExceptionalProbability
import Definitions.Def_DeletionCode_ExceptionalCountArithmetic
import Definitions.Def_DeletionCode_ExceptionalPartnerCount
set_option autoImplicit true
open DeletionCode DeletionCode.ExceptionalPartnerCount
open HeaderRecovery TaggedAnchorCount AlignmentTrace FiniteConflictGraph TraceEditData
open ExceptionalProbability ExceptionalCountArithmetic
open scoped BigOperators

theorem DeletionCode.ExceptionalPartnerCount.bad_record_of_not_separated {n r B : ℕ} (trace : Trace) (record : Record n r)
    (heq : packets record = AnchorRecords.encode trace) (hnot : ¬ Separated B trace) :
    Bad trace.matchedCount B record := by sorry
