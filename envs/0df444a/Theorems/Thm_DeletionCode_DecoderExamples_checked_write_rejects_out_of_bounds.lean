-- Prove2me | Theorems.Thm_DeletionCode_DecoderExamples_checked_write_rejects_out_of_bounds
-- name    : DeletionCode.DecoderExamples.checked_write_rejects_out_of_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:59:29.952398+00:00
-- url     : https://prove2.me/theorems/b3ee3aed-9a26-429c-9f99-114e396f0583
-- title:
--   Decoder Examples: checked write rejects out of bounds
-- statement:
--   The Decoder Examples construction uses the checked write rejects out of bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/DecoderExamples.lean#L47-L48
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/DecoderExamples.lean#L47-L48

import Definitions.Def_DeletionCode_ConcreteFill
import Definitions.Def_DeletionCode_ConcreteStart
import Mathlib.Data.List.OfFn
import Definitions.Def_DeletionCode_DecoderExamples
set_option autoImplicit true
open DeletionCode DeletionCode.DecoderExamples
open Windows PartialWords

theorem DeletionCode.DecoderExamples.checked_write_rejects_out_of_bounds :
    (writeBits empty 5 4 sampleSeed).isNone = true := by sorry
