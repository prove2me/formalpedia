-- Prove2me | Theorems.Thm_DeletionCode_HeaderRecovery_transfer_positive_seed_valid
-- name    : DeletionCode.HeaderRecovery.transfer_positive_seed_valid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:13:03.267178+00:00
-- url     : https://prove2.me/theorems/66e61cbf-a4b1-4ddc-843e-89bba82d5422
-- title:
--   Header Recovery: transfer positive seed valid
-- statement:
--   The combined letter and bounds guarantee needed for a concrete start instruction.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/HeaderRecovery.lean#L270-L281
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/HeaderRecovery.lean#L270-L281

import Definitions.Def_DeletionCode_Windows
import Definitions.Def_DeletionCode_HeaderRecovery
set_option autoImplicit true
open DeletionCode DeletionCode.HeaderRecovery
open Windows

theorem DeletionCode.HeaderRecovery.transfer_positive_seed_valid (k : ℕ) (h : Header) (long : Letters)
    (seed : Seed) (extra : Bool)
    (hrho0 : 1 ≤ h.rho) (hrho1 : h.rho ≤ k + 1)
    (hbit : long (editOffset k) = h.bit)
    (hbound : seed.offset + k ≤ positiveLength k h)
    (hseed : Agree (positivePath k h long) seed.offset seed.bits 0 k)
    (hextra : ExtensionMatches k h long seed extra) :
    (transferPositiveSeed k h seed extra).offset + k ≤ negativeLength k h ∧
      Agree (negativePath k h long) (transferPositiveSeed k h seed extra).offset
        (transferPositiveSeed k h seed extra).bits 0 k := by sorry
