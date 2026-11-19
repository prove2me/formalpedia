-- Prove2me | Theorems.Thm_DeletionCode_HeaderRecovery_negativeExtra_lt
-- name    : DeletionCode.HeaderRecovery.negativeExtra_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:07:16.346942+00:00
-- url     : https://prove2.me/theorems/83ff3caf-5f2e-4393-bde8-65d4b4cc7eb1
-- title:
--   Header Recovery: negative Extra lt
-- statement:
--   The Header Recovery construction uses the negative Extra lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/HeaderRecovery.lean#L62-L67
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/HeaderRecovery.lean#L62-L67

import Definitions.Def_DeletionCode_Windows
import Definitions.Def_DeletionCode_HeaderRecovery
set_option autoImplicit true
open DeletionCode DeletionCode.HeaderRecovery
open Windows

theorem DeletionCode.HeaderRecovery.negativeExtra_lt (k : ℕ) (h : Header)
    (hrho0 : 1 ≤ h.rho) (hrho1 : h.rho ≤ k + 1) :
    negativeExtra k h < windowLength k := by sorry
