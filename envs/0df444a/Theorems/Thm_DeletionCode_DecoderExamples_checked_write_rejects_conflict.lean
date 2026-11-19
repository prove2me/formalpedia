-- Prove2me | Theorems.Thm_DeletionCode_DecoderExamples_checked_write_rejects_conflict
-- name    : DeletionCode.DecoderExamples.checked_write_rejects_conflict
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:59:27.782526+00:00
-- url     : https://prove2.me/theorems/2deb38f9-42b9-4e26-8fd8-c348f25b62ac
-- title:
--   Decoder Examples: checked write rejects conflict
-- statement:
--   The Decoder Examples construction uses the checked write rejects conflict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/DecoderExamples.lean#L43-L45
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/DecoderExamples.lean#L43-L45

import Definitions.Def_DeletionCode_ConcreteFill
import Definitions.Def_DeletionCode_ConcreteStart
import Mathlib.Data.List.OfFn
import Definitions.Def_DeletionCode_DecoderExamples
set_option autoImplicit true
open DeletionCode DeletionCode.DecoderExamples
open Windows PartialWords

theorem DeletionCode.DecoderExamples.checked_write_rejects_conflict :
    (writeBits (putBits empty 0 (fun _ : Fin 1 => false)) 5 0
      (fun _ : Fin 1 => true)).isNone = true := by sorry
