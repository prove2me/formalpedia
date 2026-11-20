-- Prove2me | Theorems.Thm_DeletionCode_RecordSerialization_description_roundtrip
-- name    : DeletionCode.RecordSerialization.description_roundtrip
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:17:59.523937+00:00
-- url     : https://prove2.me/theorems/da29de8c-54f9-4c2d-bcd5-7322add0d338
-- title:
--   Record Serialization: description roundtrip
-- statement:
--   Serializing a bounded concrete record preserves its exact decoded result.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RecordSerialization.lean#L74-L97
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RecordSerialization.lean#L74-L97

import Definitions.Def_DeletionCode_RecordBounds
import Definitions.Def_DeletionCode_RecordPacking
import Definitions.Def_DeletionCode_RecordSerialization
set_option autoImplicit true
open DeletionCode DeletionCode.RecordSerialization
open Windows HeaderRecovery ConcreteDecoder DescriptionCount RecordCodec
open RecordPacking GeneratingModel

theorem DeletionCode.RecordSerialization.description_roundtrip (x : Letters) (n k ν c : ℕ) (hν : 1 ≤ ν)
    (header : Fin ν → Header)
    (hlo : ∀ b, 1 ≤ (header b).rho) (hhi : ∀ b, (header b).rho ≤ windowLength k)
    (roots : List (Fin ν × ℕ)) (hroots : roots.length = c)
    (hpos : ∀ b a, (b, a) ∈ roots → a < n)
    (instructions : List (Instruction (Fin ν))) (hcost : instructions.length ≤ 4 * ν)
    (hbounded : ∀ instruction ∈ instructions, InstructionBounded (windowLength k) instruction) :
    decodeDescription x n k ν c hν
      (encodeDescription n k ν c hν header hlo hhi roots hroots hpos instructions) =
      (decode x n k header roots instructions).map (dataOfOutput k header) := by sorry
