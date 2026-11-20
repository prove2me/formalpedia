-- Prove2me | Theorems.Thm_DeletionCode_GeneratingModel_EditedFamily_negative_extra
-- name    : DeletionCode.GeneratingModel.EditedFamily.negative_extra
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:58:29.070294+00:00
-- url     : https://prove2.me/theorems/1617fb3c-bc96-4224-aa10-3a3cb66211d7
-- title:
--   Edited Family: negative extra
-- statement:
--   The Edited Family construction uses the negative extra property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/GeneratingModel.lean#L38-L39
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/GeneratingModel.lean#L38-L39

import Definitions.Def_DeletionCode_ConcreteModel
import Definitions.Def_DeletionCode_SupportComponents
import Mathlib.Data.Fintype.Quotient
import Definitions.Def_DeletionCode_GeneratingModel
set_option autoImplicit true
open DeletionCode DeletionCode.GeneratingModel
open Windows HeaderRecovery PathMemory SelectedWindows RootSelection ConcreteModel
variable {B : Type*} {k : ℕ}

theorem DeletionCode.GeneratingModel.EditedFamily.negative_extra (E : EditedFamily B k) (b : B) :
    E.family.extra b false = negativeExtra k (E.header b) := by sorry
