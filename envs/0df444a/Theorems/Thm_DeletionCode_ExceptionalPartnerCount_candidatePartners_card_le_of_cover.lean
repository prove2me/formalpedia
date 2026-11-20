-- Prove2me | Theorems.Thm_DeletionCode_ExceptionalPartnerCount_candidatePartners_card_le_of_cover
-- name    : DeletionCode.ExceptionalPartnerCount.candidatePartners_card_le_of_cover
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:57:36.847993+00:00
-- url     : https://prove2.me/theorems/15e93d92-4a8a-4cba-acc0-5a8228aaff97
-- title:
--   Exceptional Partner Count: candidate Partners card le of cover
-- statement:
--   Cardinality transfer from a concrete record cover. The cover is supplied
--   by the trace encoding in the complete theorem below.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ExceptionalPartnerCount.lean#L59-L69
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ExceptionalPartnerCount.lean#L59-L69

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

theorem DeletionCode.ExceptionalPartnerCount.candidatePartners_card_le_of_cover {n : ℕ} (t k : ℕ) (x : Bits n)
    (hn : 1 ≤ n)
    (hcover : candidatePartners t k x ⊆ shortPartners t x ∪ fullPartners t k x) :
    (candidatePartners t k x).card ≤ exceptionalConstant t * windowLength k * n ^ (2 * t - 1) := by sorry
