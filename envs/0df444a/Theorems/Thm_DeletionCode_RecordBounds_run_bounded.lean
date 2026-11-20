-- Prove2me | Theorems.Thm_DeletionCode_RecordBounds_run_bounded
-- name    : DeletionCode.RecordBounds.run_bounded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:16:57.508197+00:00
-- url     : https://prove2.me/theorems/9da394df-8c2a-47b5-aef6-ebfa1cf4433b
-- title:
--   Record Bounds: run bounded
-- statement:
--   The Record Bounds construction uses the run bounded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RecordBounds.lean#L112-L126
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RecordBounds.lean#L112-L126

import Definitions.Def_DeletionCode_GeneratingRecovery
import Definitions.Def_DeletionCode_RecordCodec
import Definitions.Def_DeletionCode_RecordBounds
set_option autoImplicit true
open DeletionCode DeletionCode.RecordBounds
open Windows PartialWords HeaderRecovery PathMemory ConcreteDecoder RecordCodec
variable {B : Type*} [DecidableEq B]

theorem DeletionCode.RecordBounds.run_bounded (x : Letters) (n k : ℕ) (header : B → Header)
    (instructions : List (Instruction B)) (mem result : Bank B)
    (hs : run x n k header mem instructions = some result) :
    ∀ instruction ∈ instructions, InstructionBounded (windowLength k) instruction := by sorry
