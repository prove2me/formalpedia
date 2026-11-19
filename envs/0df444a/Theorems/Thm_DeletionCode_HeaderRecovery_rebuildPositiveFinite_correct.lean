-- Prove2me | Theorems.Thm_DeletionCode_HeaderRecovery_rebuildPositiveFinite_correct
-- name    : DeletionCode.HeaderRecovery.rebuildPositiveFinite_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:13:07.595913+00:00
-- url     : https://prove2.me/theorems/1bf9a58e-5cb1-4da4-a579-a0b20ce74f6a
-- title:
--   Header Recovery: rebuild Positive Finite correct
-- statement:
--   The Header Recovery construction uses the rebuild Positive Finite correct property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/HeaderRecovery.lean#L324-L338
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/HeaderRecovery.lean#L324-L338

import Definitions.Def_DeletionCode_Windows
import Definitions.Def_DeletionCode_HeaderRecovery
set_option autoImplicit true
open DeletionCode DeletionCode.HeaderRecovery
open Windows

theorem DeletionCode.HeaderRecovery.rebuildPositiveFinite_correct (k : ℕ) (h : Header) (long : Letters)
    (negative : Bits (negativeLength k h))
    (hrho0 : 1 ≤ h.rho) (hrho1 : h.rho ≤ k + 1)
    (hbit : long (editOffset k) = h.bit)
    (hknown : ∀ i : Fin (negativeLength k h), negative i = negativePath k h long i.val) :
    ∀ i : Fin (positiveLength k h),
      rebuildPositiveFinite k h negative i = positivePath k h long i.val := by sorry
