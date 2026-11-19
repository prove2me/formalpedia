-- Prove2me | Theorems.Thm_DeletionCode_HeaderRecovery_transfer_positive_seed_in_bounds
-- name    : DeletionCode.HeaderRecovery.transfer_positive_seed_in_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:12:59.066895+00:00
-- url     : https://prove2.me/theorems/c94fd651-e62d-4c25-9f12-25622eeff63f
-- title:
--   Header Recovery: transfer positive seed in bounds
-- statement:
--   The Header Recovery construction uses the transfer positive seed in bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/HeaderRecovery.lean#L233-L267
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/HeaderRecovery.lean#L233-L267

import Definitions.Def_DeletionCode_Windows
import Definitions.Def_DeletionCode_HeaderRecovery
set_option autoImplicit true
open DeletionCode DeletionCode.HeaderRecovery
open Windows

theorem DeletionCode.HeaderRecovery.transfer_positive_seed_in_bounds (k : ℕ) (h : Header)
    (seed : Seed) (extra : Bool)
    (hrho0 : 1 ≤ h.rho) (hrho1 : h.rho ≤ k + 1)
    (hbound : seed.offset + k ≤ positiveLength k h) :
    (transferPositiveSeed k h seed extra).offset + k ≤ negativeLength k h := by sorry
