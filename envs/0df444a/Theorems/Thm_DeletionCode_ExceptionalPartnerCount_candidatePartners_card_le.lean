-- Prove2me | Theorems.Thm_DeletionCode_ExceptionalPartnerCount_candidatePartners_card_le
-- name    : DeletionCode.ExceptionalPartnerCount.candidatePartners_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:56:39.994607+00:00
-- url     : https://prove2.me/theorems/4c3e259f-a771-4cbf-9f4c-b54c9ae1636b
-- title:
--   Exceptional Partner Count: candidate Partners card le
-- statement:
--   The combinatorial half of the paper's nonseparated-family lemma, with an
--   explicit constant depending only on t. No uniqueness assumption is needed.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ExceptionalPartnerCount.lean#L145-L147
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ExceptionalPartnerCount.lean#L145-L147

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

theorem DeletionCode.ExceptionalPartnerCount.candidatePartners_card_le {n : ℕ} (t k : ℕ) (x : Bits n) (hn : 1 ≤ n) :
    (candidatePartners t k x).card ≤ exceptionalConstant t * windowLength k * n ^ (2 * t - 1) := by sorry
