-- Prove2me | Theorems.Thm_DeletionCode_ConcreteStart_startPositive_exists
-- name    : DeletionCode.ConcreteStart.startPositive_exists
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:13:21.795777+00:00
-- url     : https://prove2.me/theorems/4bfbf9c0-ebdc-42b4-b81c-b168eb99a3c8
-- title:
--   Concrete Start: start Positive exists
-- statement:
--   One recorded Boolean always suffices, including when the seed crosses the edit.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ConcreteStart.lean#L78-L90
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ConcreteStart.lean#L78-L90

import Definitions.Def_DeletionCode_HeaderRecovery
import Definitions.Def_DeletionCode_SelectedWindows
import Definitions.Def_DeletionCode_ConcreteStart
set_option autoImplicit true
open DeletionCode DeletionCode.ConcreteStart
open Windows PartialWords SelectedWindows
open HeaderRecovery (Header negativePath positivePath negativeLength positiveLength
  transferFinite windowLength editOffset negativeExtra)

theorem DeletionCode.ConcreteStart.startPositive_exists (k : ℕ) (h : Header) (long : Letters)
    (offset : ℕ) (bits : PartialWords.Bits k) (s : Memory)
    (hrho0 : 1 ≤ h.rho) (hrho1 : h.rho ≤ k + 1)
    (hbit : long (editOffset k) = h.bit)
    (hs : Sound s (negativePath k h long) (negativeLength k h))
    (hbound : offset + k ≤ positiveLength k h)
    (hseed : ∀ i : Fin k, positivePath k h long (offset + i.val) = bits i) :
    ∃ extra t, startPositive k h offset bits extra s = some t ∧
      StartedCorrectly k h long s t := by sorry
