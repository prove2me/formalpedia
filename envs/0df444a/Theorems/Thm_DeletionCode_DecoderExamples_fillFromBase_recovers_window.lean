-- Prove2me | Theorems.Thm_DeletionCode_DecoderExamples_fillFromBase_recovers_window
-- name    : DeletionCode.DecoderExamples.fillFromBase_recovers_window
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:59:13.823358+00:00
-- url     : https://prove2.me/theorems/9e45aaf1-3ad2-4ff7-97ea-a0e0a65dc5b0
-- title:
--   Decoder Examples: fill From Base recovers window
-- statement:
--   The Decoder Examples construction uses the fill From Base recovers window property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/DecoderExamples.lean#L33-L36
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/DecoderExamples.lean#L33-L36

import Definitions.Def_DeletionCode_ConcreteFill
import Definitions.Def_DeletionCode_ConcreteStart
import Mathlib.Data.List.OfFn
import Definitions.Def_DeletionCode_DecoderExamples
set_option autoImplicit true
open DeletionCode DeletionCode.DecoderExamples
open Windows PartialWords

theorem DeletionCode.DecoderExamples.fillFromBase_recovers_window :
    ((ConcreteFill.fillFromBase sampleWord 10 3 5 sampleMemory 5 0 1).bind
      (fun memory => (readBits memory 0 5).map (fun bits => List.ofFn bits))) =
      some [false, true, false, true, true] := by sorry
