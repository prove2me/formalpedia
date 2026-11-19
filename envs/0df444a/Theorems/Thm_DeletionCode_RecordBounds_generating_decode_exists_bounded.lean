-- Prove2me | Theorems.Thm_DeletionCode_RecordBounds_generating_decode_exists_bounded
-- name    : DeletionCode.RecordBounds.generating_decode_exists_bounded
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:17:23.725034+00:00
-- url     : https://prove2.me/theorems/da700a68-697c-4969-9fdc-09f6a9245d45
-- title:
--   Record Bounds: generating decode exists bounded
-- statement:
--   The successful generating-family record automatically satisfies all field bounds.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RecordBounds.lean#L173-L186
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RecordBounds.lean#L173-L186

import Definitions.Def_DeletionCode_GeneratingRecovery
import Definitions.Def_DeletionCode_RecordCodec
import Definitions.Def_DeletionCode_RecordBounds
set_option autoImplicit true
open DeletionCode DeletionCode.RecordBounds
open Windows PartialWords HeaderRecovery PathMemory ConcreteDecoder RecordCodec
variable {B : Type*} [DecidableEq B]

theorem DeletionCode.RecordBounds.generating_decode_exists_bounded [Fintype B]
    (E : GeneratingModel.EditedFamily B k) (x : Letters) (n : ℕ)
    (hx : KUnique x n k) (hg : E.family.Generating x n (windowLength k)) :
    ∃ roots instructions,
      roots.length = Fintype.card (SupportComponents.GraphComponents E.family (windowLength k)) ∧
      instructions.length ≤ 4 * Fintype.card B ∧
      decode x n k E.header roots instructions =
        some (fun b i => negativePath k (E.header b) (E.long b) i.val) ∧
      (∀ b a, (b, a) ∈ roots → a < n) ∧
      (∀ instruction ∈ instructions, InstructionBounded (windowLength k) instruction) := by sorry
