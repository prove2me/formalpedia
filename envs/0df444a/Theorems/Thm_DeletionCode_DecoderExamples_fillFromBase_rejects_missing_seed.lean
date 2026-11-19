-- Prove2me | Theorems.Thm_DeletionCode_DecoderExamples_fillFromBase_rejects_missing_seed
-- name    : DeletionCode.DecoderExamples.fillFromBase_rejects_missing_seed
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:59:44.651855+00:00
-- url     : https://prove2.me/theorems/a6406b7d-2cfe-4448-85d3-bfb47fa58bf5
-- title:
--   Decoder Examples: fill From Base rejects missing seed
-- statement:
--   The Decoder Examples construction uses the fill From Base rejects missing seed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/DecoderExamples.lean#L55-L56
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/DecoderExamples.lean#L55-L56

import Definitions.Def_DeletionCode_ConcreteFill
import Definitions.Def_DeletionCode_ConcreteStart
import Mathlib.Data.List.OfFn
import Definitions.Def_DeletionCode_DecoderExamples
set_option autoImplicit true
open DeletionCode DeletionCode.DecoderExamples
open Windows PartialWords

theorem DeletionCode.DecoderExamples.fillFromBase_rejects_missing_seed :
    (ConcreteFill.fillFromBase sampleWord 10 3 5 empty 5 0 1).isNone = true := by sorry
