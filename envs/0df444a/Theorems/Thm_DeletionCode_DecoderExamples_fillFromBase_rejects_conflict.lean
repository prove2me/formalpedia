-- Prove2me | Theorems.Thm_DeletionCode_DecoderExamples_fillFromBase_rejects_conflict
-- name    : DeletionCode.DecoderExamples.fillFromBase_rejects_conflict
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:59:24.406976+00:00
-- url     : https://prove2.me/theorems/c42b4284-ea81-48d2-be67-f07cac6caddd
-- title:
--   Decoder Examples: fill From Base rejects conflict
-- statement:
--   A conflicting bit outside the seed is detected when the whole window is written.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/DecoderExamples.lean#L39-L41
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/DecoderExamples.lean#L39-L41

import Definitions.Def_DeletionCode_ConcreteFill
import Definitions.Def_DeletionCode_ConcreteStart
import Mathlib.Data.List.OfFn
import Definitions.Def_DeletionCode_DecoderExamples
set_option autoImplicit true
open DeletionCode DeletionCode.DecoderExamples
open Windows PartialWords

theorem DeletionCode.DecoderExamples.fillFromBase_rejects_conflict :
    (ConcreteFill.fillFromBase sampleWord 10 3 5
      (putBits sampleMemory 0 (fun _ : Fin 1 => true)) 5 0 1).isNone = true := by sorry
