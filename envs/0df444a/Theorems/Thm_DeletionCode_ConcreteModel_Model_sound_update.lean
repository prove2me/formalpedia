-- Prove2me | Theorems.Thm_DeletionCode_ConcreteModel_Model_sound_update
-- name    : DeletionCode.ConcreteModel.Model.sound_update
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:09:46.432387+00:00
-- url     : https://prove2.me/theorems/dda0b7b4-8b41-4130-bb46-747490952bb6
-- title:
--   Model: sound update
-- statement:
--   The Model construction uses the sound update property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ConcreteModel.lean#L68-L77
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ConcreteModel.lean#L68-L77

import Definitions.Def_DeletionCode_ConcreteDecoder
import Definitions.Def_DeletionCode_RootSelection
import Definitions.Def_DeletionCode_ConcreteModel
set_option autoImplicit true
open DeletionCode DeletionCode.ConcreteModel
open Windows HeaderRecovery SelectedWindows PartialWords PathMemory ConcreteDecoder
variable {B : Type*} {x : Letters} {n k : ℕ}

theorem DeletionCode.ConcreteModel.Model.sound_update [DecidableEq B] (M : Model B x n k)
    (mem : Bank B) (hs : M.Sound mem) (b : B) (t : Memory)
    (ht : PartialWords.Sound t (negativePath k (M.header b) (M.long b))
      (negativeLength k (M.header b))) : M.Sound (Function.update mem b t) := by sorry
