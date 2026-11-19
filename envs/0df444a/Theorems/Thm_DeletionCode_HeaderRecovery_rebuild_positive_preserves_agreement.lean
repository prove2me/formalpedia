-- Prove2me | Theorems.Thm_DeletionCode_HeaderRecovery_rebuild_positive_preserves_agreement
-- name    : DeletionCode.HeaderRecovery.rebuild_positive_preserves_agreement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:12:11.019717+00:00
-- url     : https://prove2.me/theorems/7655d000-62ef-4a12-904a-b1d859aa00f8
-- title:
--   Header Recovery: rebuild positive preserves agreement
-- statement:
--   Rebuilding depends only on the finite negative word, not its unused tail.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/HeaderRecovery.lean#L86-L119
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/HeaderRecovery.lean#L86-L119

import Definitions.Def_DeletionCode_Windows
import Definitions.Def_DeletionCode_HeaderRecovery
set_option autoImplicit true
open DeletionCode DeletionCode.HeaderRecovery
open Windows

theorem DeletionCode.HeaderRecovery.rebuild_positive_preserves_agreement (k : ℕ) (h : Header) (p q : Letters)
    (hrho0 : 1 ≤ h.rho) (hrho1 : h.rho ≤ k + 1)
    (hknown : Agree p 0 q 0 (negativeLength k h)) :
    Agree (rebuildPositive k h p) 0 (rebuildPositive k h q) 0 (positiveLength k h) := by sorry
