-- Prove2me | Theorems.Thm_DeletionCode_HeaderRecovery_rebuild_positive_from_known_negative
-- name    : DeletionCode.HeaderRecovery.rebuild_positive_from_known_negative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:11:34.081226+00:00
-- url     : https://prove2.me/theorems/6c2dcdc2-de63-4c51-945a-4b9a1e373753
-- title:
--   Header Recovery: rebuild positive from known negative
-- statement:
--   Correct finite negative letters suffice to recover the entire positive word.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/HeaderRecovery.lean#L122-L130
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/HeaderRecovery.lean#L122-L130

import Definitions.Def_DeletionCode_Windows
import Definitions.Def_DeletionCode_HeaderRecovery
set_option autoImplicit true
open DeletionCode DeletionCode.HeaderRecovery
open Windows

theorem DeletionCode.HeaderRecovery.rebuild_positive_from_known_negative (k : ℕ) (h : Header)
    (long known : Letters)
    (hrho0 : 1 ≤ h.rho) (hrho1 : h.rho ≤ k + 1)
    (hbit : long (editOffset k) = h.bit)
    (hknown : Agree known 0 (negativePath k h long) 0 (negativeLength k h)) :
    Agree (rebuildPositive k h known) 0 (positivePath k h long) 0 (positiveLength k h) := by sorry
