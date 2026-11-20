-- Prove2me | Theorems.Thm_DeletionCode_ExceptionalPartnerCount_fullPartners_card_le
-- name    : DeletionCode.ExceptionalPartnerCount.fullPartners_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:57:29.279561+00:00
-- url     : https://prove2.me/theorems/16834656-7a91-4e37-8f4f-090a94025575
-- title:
--   Exceptional Partner Count: full Partners card le
-- statement:
--   The Exceptional Partner Count construction uses the full Partners card le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ExceptionalPartnerCount.lean#L47-L55
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ExceptionalPartnerCount.lean#L47-L55

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

theorem DeletionCode.ExceptionalPartnerCount.fullPartners_card_le {n : ℕ} (t k : ℕ) (x : Bits n) :
    (fullPartners t k x).card ≤
      (2 * t) * (2 * t + 2) * (2 * (4 * windowLength k)) * n ^ (2 * t - 1) * 4 ^ (2 * t) := by sorry
