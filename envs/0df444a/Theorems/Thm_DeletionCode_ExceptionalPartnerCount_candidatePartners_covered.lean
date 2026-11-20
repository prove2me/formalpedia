-- Prove2me | Theorems.Thm_DeletionCode_ExceptionalPartnerCount_candidatePartners_covered
-- name    : DeletionCode.ExceptionalPartnerCount.candidatePartners_covered
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:56:41.80517+00:00
-- url     : https://prove2.me/theorems/3ef3d746-d639-4846-9b6f-9305066d3f20
-- title:
--   Exceptional Partner Count: candidate Partners covered
-- statement:
--   Every actual exceptional partner is the decoded image of a short record
--   or a full-size record with a constrained anchor.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ExceptionalPartnerCount.lean#L110-L141
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ExceptionalPartnerCount.lean#L110-L141

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

theorem DeletionCode.ExceptionalPartnerCount.candidatePartners_covered {n : ℕ} (t k : ℕ) (x : Bits n) :
    candidatePartners t k x ⊆ shortPartners t x ∪ fullPartners t k x := by sorry
