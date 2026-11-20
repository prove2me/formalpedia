-- Prove2me | Theorems.Thm_DeletionCode_DecoderExamples_seed_lookup_recovers_window
-- name    : DeletionCode.DecoderExamples.seed_lookup_recovers_window
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:58:59.528117+00:00
-- url     : https://prove2.me/theorems/e6a3c473-21ab-489f-98e8-af2549c07ff3
-- title:
--   Decoder Examples: seed lookup recovers window
-- statement:
--   The Decoder Examples construction uses the seed lookup recovers window property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/DecoderExamples.lean#L29-L31
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/DecoderExamples.lean#L29-L31

import Definitions.Def_DeletionCode_ConcreteFill
import Definitions.Def_DeletionCode_ConcreteStart
import Mathlib.Data.List.OfFn
import Definitions.Def_DeletionCode_DecoderExamples
set_option autoImplicit true
open DeletionCode DeletionCode.DecoderExamples
open Windows PartialWords

theorem DeletionCode.DecoderExamples.seed_lookup_recovers_window :
    (SeedLookup.recoverWindow sampleWord 10 3 5 1 sampleSeed).map
      (fun bits => List.ofFn bits) = some [false, true, false, true, true] := by sorry
