-- Prove2me | Theorems.Thm_DeletionCode_EditRigidity_one_edit_spectrum_boolean
-- name    : DeletionCode.EditRigidity.one_edit_spectrum_boolean
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:16:28.318793+00:00
-- url     : https://prove2.me/theorems/abb36201-cfcb-40ca-a03a-62e77898b1f4
-- title:
--   Edit Rigidity: one edit spectrum boolean
-- statement:
--   The integer L-spectrum remains Boolean after any one valid edit.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/EditRigidity.lean#L61-L66
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/EditRigidity.lean#L61-L66

import Definitions.Def_DeletionCode_SingleEditOrigins
import Definitions.Def_DeletionCode_TwoEditWindows
import Definitions.Def_DeletionCode_SpectrumPath
import Definitions.Def_DeletionCode_EditRigidity
set_option autoImplicit true
open DeletionCode DeletionCode.EditRigidity
open Windows HeaderRecovery SingleEditOrigins

theorem DeletionCode.EditRigidity.one_edit_spectrum_boolean {n k : ℕ} (hk : 1 ≤ k) (x : Letters)
    (hx : KUnique x n k) (e : Edit) (he : e.Valid n) :
    ∀ g, SignedSupport.wordSpectrum (e.word x) (e.outputLength n) (windowLength k) g = 0 ∨
      SignedSupport.wordSpectrum (e.word x) (e.outputLength n) (windowLength k) g = 1 := by sorry
