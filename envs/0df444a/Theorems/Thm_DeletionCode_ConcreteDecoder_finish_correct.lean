-- Prove2me | Theorems.Thm_DeletionCode_ConcreteDecoder_finish_correct
-- name    : DeletionCode.ConcreteDecoder.finish_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:13:59.256496+00:00
-- url     : https://prove2.me/theorems/569f8bd7-980e-450d-bb07-b01234d8fcf1
-- title:
--   Concrete Decoder: finish correct
-- statement:
--   Sound completed memory produces exactly the finite target negative paths.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ConcreteDecoder.lean#L108-L123
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ConcreteDecoder.lean#L108-L123

import Definitions.Def_DeletionCode_ConcreteFill
import Definitions.Def_DeletionCode_ConcreteStart
import Definitions.Def_DeletionCode_PathMemory
import Definitions.Def_DeletionCode_ConcreteDecoder
set_option autoImplicit true
open DeletionCode DeletionCode.ConcreteDecoder
open Windows PartialWords HeaderRecovery SelectedWindows
variable {B : Type*} [DecidableEq B]

theorem DeletionCode.ConcreteDecoder.finish_correct [Fintype B] (k : ℕ) (header : B → Header)
    (long : B → Letters) (mem : Bank B)
    (hs : ∀ b, Sound (mem b) (negativePath k (header b) (long b))
      (negativeLength k (header b)))
    (hknown : ∀ b, WindowKnown (mem b) 0 (negativeLength k (header b))) :
    finish k header mem = some (fun b i => negativePath k (header b) (long b) i.val) := by sorry
