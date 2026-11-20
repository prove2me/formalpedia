-- Prove2me | Theorems.Thm_DeletionCode_ExceptionalPartnerCount_shortPartners_card_le
-- name    : DeletionCode.ExceptionalPartnerCount.shortPartners_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:56:49.134786+00:00
-- url     : https://prove2.me/theorems/727d498b-b547-480b-bcf4-36006de01284
-- title:
--   Exceptional Partner Count: short Partners card le
-- statement:
--   The Exceptional Partner Count construction uses the short Partners card le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ExceptionalPartnerCount.lean#L36-L45
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ExceptionalPartnerCount.lean#L36-L45

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

theorem DeletionCode.ExceptionalPartnerCount.shortPartners_card_le {n : ℕ} (t : ℕ) (x : Bits n) :
    (shortPartners t x).card ≤ ∑ d ∈ Finset.range t, n ^ (2 * d) * 4 ^ (2 * d) := by sorry
