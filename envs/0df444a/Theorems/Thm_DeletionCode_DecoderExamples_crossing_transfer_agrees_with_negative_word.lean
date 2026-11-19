-- Prove2me | Theorems.Thm_DeletionCode_DecoderExamples_crossing_transfer_agrees_with_negative_word
-- name    : DeletionCode.DecoderExamples.crossing_transfer_agrees_with_negative_word
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:59:58.597933+00:00
-- url     : https://prove2.me/theorems/631fe208-3c39-41b1-bf3d-025a77a055cc
-- title:
--   Decoder Examples: crossing transfer agrees with negative word
-- statement:
--   The Decoder Examples construction uses the crossing transfer agrees with negative word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/DecoderExamples.lean#L74-L79
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/DecoderExamples.lean#L74-L79

import Definitions.Def_DeletionCode_ConcreteFill
import Definitions.Def_DeletionCode_ConcreteStart
import Mathlib.Data.List.OfFn
import Definitions.Def_DeletionCode_DecoderExamples
set_option autoImplicit true
open DeletionCode DeletionCode.DecoderExamples
open Windows PartialWords

theorem DeletionCode.DecoderExamples.crossing_transfer_agrees_with_negative_word :
    let result := HeaderRecovery.transferFinite 1 crossingHeader 5
      (fun _ : Fin 1 => true) false
    List.ofFn result.2 = List.ofFn (fun i : Fin 1 =>
      HeaderRecovery.negativePath 1 crossingHeader crossingLong (result.1 + i.val)) := by sorry
