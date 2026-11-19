-- Prove2me | Theorems.Thm_DeletionCode_DecoderExamples_crossing_transfer_uses_extension_bit
-- name    : DeletionCode.DecoderExamples.crossing_transfer_uses_extension_bit
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:59:58.955081+00:00
-- url     : https://prove2.me/theorems/d8c7aebf-0723-4644-87f0-3a0e06c9de72
-- title:
--   Decoder Examples: crossing transfer uses extension bit
-- statement:
--   The Decoder Examples construction uses the crossing transfer uses extension bit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/DecoderExamples.lean#L69-L72
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/DecoderExamples.lean#L69-L72

import Definitions.Def_DeletionCode_ConcreteFill
import Definitions.Def_DeletionCode_ConcreteStart
import Mathlib.Data.List.OfFn
import Definitions.Def_DeletionCode_DecoderExamples
set_option autoImplicit true
open DeletionCode DeletionCode.DecoderExamples
open Windows PartialWords

theorem DeletionCode.DecoderExamples.crossing_transfer_uses_extension_bit :
    let result := HeaderRecovery.transferFinite 1 crossingHeader 5
      (fun _ : Fin 1 => true) false
    (result.1, List.ofFn result.2) = (5, [false]) := by sorry
