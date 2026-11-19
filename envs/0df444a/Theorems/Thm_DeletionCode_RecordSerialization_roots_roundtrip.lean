-- Prove2me | Theorems.Thm_DeletionCode_RecordSerialization_roots_roundtrip
-- name    : DeletionCode.RecordSerialization.roots_roundtrip
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:17:30.008987+00:00
-- url     : https://prove2.me/theorems/e4a0a6cb-fb16-4dfc-8f8e-deaa77018699
-- title:
--   Record Serialization: roots roundtrip
-- statement:
--   The Record Serialization construction uses the roots roundtrip property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RecordSerialization.lean#L46-L52
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RecordSerialization.lean#L46-L52

import Definitions.Def_DeletionCode_RecordBounds
import Definitions.Def_DeletionCode_RecordPacking
import Definitions.Def_DeletionCode_RecordSerialization
set_option autoImplicit true
open DeletionCode DeletionCode.RecordSerialization
open Windows HeaderRecovery ConcreteDecoder DescriptionCount RecordCodec
open RecordPacking GeneratingModel

theorem DeletionCode.RecordSerialization.roots_roundtrip (n ν c : ℕ) (roots : List (Fin ν × ℕ))
    (hlen : roots.length = c) (hpos : ∀ b a, (b, a) ∈ roots → a < n) :
    rootsOfVectors (rootVectors n ν c roots hlen hpos).1
      (rootVectors n ν c roots hlen hpos).2 = roots := by sorry
