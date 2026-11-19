-- Prove2me | Theorems.Thm_DeletionCode_ConcreteStart_startNegative_correct
-- name    : DeletionCode.ConcreteStart.startNegative_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:13:19.773911+00:00
-- url     : https://prove2.me/theorems/f0732535-c39c-43e4-9e44-32d909c73ce2
-- title:
--   Concrete Start: start Negative correct
-- statement:
--   The Concrete Start construction uses the start Negative correct property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ConcreteStart.lean#L32-L46
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ConcreteStart.lean#L32-L46

import Definitions.Def_DeletionCode_HeaderRecovery
import Definitions.Def_DeletionCode_SelectedWindows
import Definitions.Def_DeletionCode_ConcreteStart
set_option autoImplicit true
open DeletionCode DeletionCode.ConcreteStart
open Windows PartialWords SelectedWindows
open HeaderRecovery (Header negativePath positivePath negativeLength positiveLength
  transferFinite windowLength editOffset negativeExtra)

theorem DeletionCode.ConcreteStart.startNegative_correct (k : ℕ) (h : Header) (long : Letters)
    (offset : ℕ) (bits : PartialWords.Bits k) (s : Memory)
    (hrho0 : 1 ≤ h.rho) (hrho1 : h.rho ≤ k + 1)
    (hs : Sound s (negativePath k h long) (negativeLength k h))
    (hbound : offset + k ≤ negativeLength k h)
    (hseed : PartialWords.Matches bits (negativePath k h long) offset) :
    ∃ t, startNegative k h offset bits s = some t ∧ StartedCorrectly k h long s t := by sorry
