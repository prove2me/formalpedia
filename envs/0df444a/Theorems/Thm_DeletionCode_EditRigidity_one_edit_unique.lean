-- Prove2me | Theorems.Thm_DeletionCode_EditRigidity_one_edit_unique
-- name    : DeletionCode.EditRigidity.one_edit_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:20:00.606946+00:00
-- url     : https://prove2.me/theorems/f5632a09-f30e-4b8b-8a51-852940fe5138
-- title:
--   Edit Rigidity: one edit unique
-- statement:
--   No two distinct (L-1)-windows of a word one edit away from x coincide.
--   The injectivity of surviving source positions is proved from the edit.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/EditRigidity.lean#L51-L58
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/EditRigidity.lean#L51-L58

import Definitions.Def_DeletionCode_SingleEditOrigins
import Definitions.Def_DeletionCode_TwoEditWindows
import Definitions.Def_DeletionCode_SpectrumPath
import Definitions.Def_DeletionCode_EditRigidity
set_option autoImplicit true
open DeletionCode DeletionCode.EditRigidity
open Windows HeaderRecovery SingleEditOrigins

theorem DeletionCode.EditRigidity.one_edit_unique {n k : ℕ} (hk : 1 ≤ k) (x : Letters)
    (hx : KUnique x n k) (e : Edit) (he : e.Valid n) :
    KUnique (e.word x) (e.outputLength n) (windowLength k - 1) := by sorry
