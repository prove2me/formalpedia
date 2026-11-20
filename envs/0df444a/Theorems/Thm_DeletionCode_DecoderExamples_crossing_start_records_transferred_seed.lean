-- Prove2me | Theorems.Thm_DeletionCode_DecoderExamples_crossing_start_records_transferred_seed
-- name    : DeletionCode.DecoderExamples.crossing_start_records_transferred_seed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:00:01.480575+00:00
-- url     : https://prove2.me/theorems/3e4c6ae4-4dbb-4efa-b60d-f6d6ae380148
-- title:
--   Decoder Examples: crossing start records transferred seed
-- statement:
--   The Decoder Examples construction uses the crossing start records transferred seed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/DecoderExamples.lean#L81-L84
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/DecoderExamples.lean#L81-L84

import Definitions.Def_DeletionCode_ConcreteFill
import Definitions.Def_DeletionCode_ConcreteStart
import Mathlib.Data.List.OfFn
import Definitions.Def_DeletionCode_DecoderExamples
set_option autoImplicit true
open DeletionCode DeletionCode.DecoderExamples
open Windows PartialWords

theorem DeletionCode.DecoderExamples.crossing_start_records_transferred_seed :
    ((ConcreteStart.startPositive 1 crossingHeader 5 (fun _ : Fin 1 => true) false empty).bind
      (fun memory => (readBits memory 5 1).map (fun bits => List.ofFn bits))) =
      some [false] := by sorry
