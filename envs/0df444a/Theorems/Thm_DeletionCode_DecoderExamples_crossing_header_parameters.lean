-- Prove2me | Theorems.Thm_DeletionCode_DecoderExamples_crossing_header_parameters
-- name    : DeletionCode.DecoderExamples.crossing_header_parameters
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:59:49.8712+00:00
-- url     : https://prove2.me/theorems/d66bdaa8-d186-49c0-a43f-79009d81e564
-- title:
--   Decoder Examples: crossing header parameters
-- statement:
--   The Decoder Examples construction uses the crossing header parameters property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/DecoderExamples.lean#L64-L67
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/DecoderExamples.lean#L64-L67

import Definitions.Def_DeletionCode_ConcreteFill
import Definitions.Def_DeletionCode_ConcreteStart
import Mathlib.Data.List.OfFn
import Definitions.Def_DeletionCode_DecoderExamples
set_option autoImplicit true
open DeletionCode DeletionCode.DecoderExamples
open Windows PartialWords

theorem DeletionCode.DecoderExamples.crossing_header_parameters :
    1 ≤ crossingHeader.rho ∧ crossingHeader.rho ≤ 1 + 1 ∧
      HeaderRecovery.windowLength 1 = 6 ∧
      crossingLong (HeaderRecovery.editOffset 1) = crossingHeader.bit := by sorry
