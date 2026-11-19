-- Prove2me | Theorems.Thm_DeletionCode_ConcreteDecoder_run_append
-- name    : DeletionCode.ConcreteDecoder.run_append
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:57:30.31581+00:00
-- url     : https://prove2.me/theorems/7b3b4642-dee5-4e4c-be89-f42e8c305466
-- title:
--   Concrete Decoder: run append
-- statement:
--   Running a concatenated record is ordinary sequential composition.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ConcreteDecoder.lean#L126-L136
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ConcreteDecoder.lean#L126-L136

import Definitions.Def_DeletionCode_ConcreteFill
import Definitions.Def_DeletionCode_ConcreteStart
import Definitions.Def_DeletionCode_PathMemory
import Definitions.Def_DeletionCode_ConcreteDecoder
set_option autoImplicit true
open DeletionCode DeletionCode.ConcreteDecoder
open Windows PartialWords HeaderRecovery SelectedWindows
variable {B : Type*} [DecidableEq B]

theorem DeletionCode.ConcreteDecoder.run_append (x : Letters) (n k : ℕ) (header : B → Header)
    (first second : List (Instruction B)) (mem : Bank B) :
    run x n k header mem (first ++ second) =
      (run x n k header mem first).bind (fun t => run x n k header t second) := by sorry
