-- Prove2me | Theorems.Thm_DeletionCode_HeaderRecovery_negativeLength_eq
-- name    : DeletionCode.HeaderRecovery.negativeLength_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:07:18.464812+00:00
-- url     : https://prove2.me/theorems/f1f07446-ea28-4a2c-b862-f8f8561a760b
-- title:
--   Header Recovery: negative Length eq
-- statement:
--   The Header Recovery construction uses the negative Length eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/HeaderRecovery.lean#L55-L60
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/HeaderRecovery.lean#L55-L60

import Definitions.Def_DeletionCode_Windows
import Definitions.Def_DeletionCode_HeaderRecovery
set_option autoImplicit true
open DeletionCode DeletionCode.HeaderRecovery
open Windows

theorem DeletionCode.HeaderRecovery.negativeLength_eq (k : ℕ) (h : Header)
    (hrho0 : 1 ≤ h.rho) (hrho1 : h.rho ≤ k + 1) :
    negativeLength k h = windowLength k + negativeExtra k h := by sorry
