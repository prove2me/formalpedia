-- Prove2me | Theorems.Thm_DeletionCode_ExceptionalPartnerCount_decodeWord_eq
-- name    : DeletionCode.ExceptionalPartnerCount.decodeWord_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:56:39.523846+00:00
-- url     : https://prove2.me/theorems/a0279e62-a68f-4e2f-b340-5984bbbc5cda
-- title:
--   Exceptional Partner Count: decode Word eq
-- statement:
--   The Exceptional Partner Count construction uses the decode Word eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ExceptionalPartnerCount.lean#L20-L24
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ExceptionalPartnerCount.lean#L20-L24

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

theorem DeletionCode.ExceptionalPartnerCount.decodeWord_eq {n r : ℕ} (x y : Bits n) (record : Record n r)
    (h : AnchorRecords.decode (List.ofFn x) (packets record) = List.ofFn y) :
    decodeWord x record = y := by sorry
