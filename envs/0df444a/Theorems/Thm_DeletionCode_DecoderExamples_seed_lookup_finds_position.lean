-- Prove2me | Theorems.Thm_DeletionCode_DecoderExamples_seed_lookup_finds_position
-- name    : DeletionCode.DecoderExamples.seed_lookup_finds_position
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:58:42.514187+00:00
-- url     : https://prove2.me/theorems/e6408b1f-7b13-49fa-8b57-09d1b32f31e1
-- title:
--   Decoder Examples: seed lookup finds position
-- statement:
--   The Decoder Examples construction uses the seed lookup finds position property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/DecoderExamples.lean#L26-L27
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/DecoderExamples.lean#L26-L27

import Definitions.Def_DeletionCode_ConcreteFill
import Definitions.Def_DeletionCode_ConcreteStart
import Mathlib.Data.List.OfFn
import Definitions.Def_DeletionCode_DecoderExamples
set_option autoImplicit true
open DeletionCode DeletionCode.DecoderExamples
open Windows PartialWords

theorem DeletionCode.DecoderExamples.seed_lookup_finds_position :
    SeedLookup.lookup sampleWord 10 3 5 1 sampleSeed = some 2 := by sorry
