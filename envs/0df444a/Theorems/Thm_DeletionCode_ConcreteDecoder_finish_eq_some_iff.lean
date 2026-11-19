-- Prove2me | Theorems.Thm_DeletionCode_ConcreteDecoder_finish_eq_some_iff
-- name    : DeletionCode.ConcreteDecoder.finish_eq_some_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:14:00.356903+00:00
-- url     : https://prove2.me/theorems/91c31146-fbba-44b7-b8be-a83bcdf72c30
-- title:
--   Concrete Decoder: finish eq some iff
-- statement:
--   The Concrete Decoder construction uses the finish eq some iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ConcreteDecoder.lean#L81-L105
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ConcreteDecoder.lean#L81-L105

import Definitions.Def_DeletionCode_ConcreteFill
import Definitions.Def_DeletionCode_ConcreteStart
import Definitions.Def_DeletionCode_PathMemory
import Definitions.Def_DeletionCode_ConcreteDecoder
set_option autoImplicit true
open DeletionCode DeletionCode.ConcreteDecoder
open Windows PartialWords HeaderRecovery SelectedWindows
variable {B : Type*} [DecidableEq B]

theorem DeletionCode.ConcreteDecoder.finish_eq_some_iff [Fintype B] (k : ℕ) (header : B → Header)
    (mem : Bank B) (output : Output k header) :
    finish k header mem = some output ↔
      ∀ b, readBits (mem b) 0 (negativeLength k (header b)) = some (output b) := by sorry
