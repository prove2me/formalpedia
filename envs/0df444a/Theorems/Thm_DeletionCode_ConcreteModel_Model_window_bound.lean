-- Prove2me | Theorems.Thm_DeletionCode_ConcreteModel_Model_window_bound
-- name    : DeletionCode.ConcreteModel.Model.window_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:09:44.501814+00:00
-- url     : https://prove2.me/theorems/9c03026b-a704-4994-bbe1-67d898982cf9
-- title:
--   Model: window bound
-- statement:
--   The Model construction uses the window bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ConcreteModel.lean#L54-L59
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ConcreteModel.lean#L54-L59

import Definitions.Def_DeletionCode_ConcreteDecoder
import Definitions.Def_DeletionCode_RootSelection
import Definitions.Def_DeletionCode_ConcreteModel
set_option autoImplicit true
open DeletionCode DeletionCode.ConcreteModel
open Windows HeaderRecovery SelectedWindows PartialWords PathMemory ConcreteDecoder
variable {B : Type*} {x : Letters} {n k : ℕ}

theorem DeletionCode.ConcreteModel.Model.window_bound (M : Model B x n k) (b : B) (w : Recovery.Slot) :
    windowStart (negativeExtra k (M.header b)) w + windowLength k ≤
      negativeLength k (M.header b) := by sorry
