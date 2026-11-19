-- Prove2me | Theorems.Thm_DeletionCode_HeaderRecovery_transferFinite_valid
-- name    : DeletionCode.HeaderRecovery.transferFinite_valid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:12:58.477755+00:00
-- url     : https://prove2.me/theorems/ae5a0da7-1052-4d10-9604-e6f4c77c525c
-- title:
--   Header Recovery: transfer Finite valid
-- statement:
--   The Header Recovery construction uses the transfer Finite valid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/HeaderRecovery.lean#L295-L317
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/HeaderRecovery.lean#L295-L317

import Definitions.Def_DeletionCode_Windows
import Definitions.Def_DeletionCode_HeaderRecovery
set_option autoImplicit true
open DeletionCode DeletionCode.HeaderRecovery
open Windows

theorem DeletionCode.HeaderRecovery.transferFinite_valid (k : ℕ) (h : Header) (long : Letters)
    (offset : ℕ) (bits : Bits k) (extra : Bool)
    (hrho0 : 1 ≤ h.rho) (hrho1 : h.rho ≤ k + 1)
    (hbit : long (editOffset k) = h.bit)
    (hbound : offset + k ≤ positiveLength k h)
    (hseed : ∀ i : Fin k, positivePath k h long (offset + i.val) = bits i)
    (hextra : h.orientation = .insertion → offset ≤ editOffset k →
      editOffset k < offset + k →
        extra = negativePath k h long (offset + k - 1)) :
    (transferFinite k h offset bits extra).1 + k ≤ negativeLength k h ∧
      ∀ i : Fin k,
        negativePath k h long ((transferFinite k h offset bits extra).1 + i.val) =
          (transferFinite k h offset bits extra).2 i := by sorry
