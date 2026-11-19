-- Prove2me | Theorems.Thm_DeletionCode_DecoderExamples_fillFromBase_rejects_out_of_bounds
-- name    : DeletionCode.DecoderExamples.fillFromBase_rejects_out_of_bounds
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:59:44.578946+00:00
-- url     : https://prove2.me/theorems/8bf87625-20f4-417f-b53f-e0b49373ad91
-- title:
--   Decoder Examples: fill From Base rejects out of bounds
-- statement:
--   The same valid lookup must still reject a destination that is too short.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/DecoderExamples.lean#L51-L53
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/DecoderExamples.lean#L51-L53

import Definitions.Def_DeletionCode_ConcreteFill
import Definitions.Def_DeletionCode_ConcreteStart
import Mathlib.Data.List.OfFn
import Definitions.Def_DeletionCode_DecoderExamples
set_option autoImplicit true
open DeletionCode DeletionCode.DecoderExamples
open Windows PartialWords

theorem DeletionCode.DecoderExamples.fillFromBase_rejects_out_of_bounds :
    (ConcreteFill.fillFromBase sampleWord 10 3 5 sampleMemory 4 0 1).isNone = true := by sorry
