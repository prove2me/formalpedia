-- Prove2me | Theorems.Thm_DeletionCode_ConcreteStart_startPositive_correct
-- name    : DeletionCode.ConcreteStart.startPositive_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:13:23.003019+00:00
-- url     : https://prove2.me/theorems/e69ea60c-b023-42bb-b89e-10ee0f03e523
-- title:
--   Concrete Start: start Positive correct
-- statement:
--   The positive start preserves all known data and creates a real selected seed.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ConcreteStart.lean#L49-L75
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ConcreteStart.lean#L49-L75

import Definitions.Def_DeletionCode_HeaderRecovery
import Definitions.Def_DeletionCode_SelectedWindows
import Definitions.Def_DeletionCode_ConcreteStart
set_option autoImplicit true
open DeletionCode DeletionCode.ConcreteStart
open Windows PartialWords SelectedWindows
open HeaderRecovery (Header negativePath positivePath negativeLength positiveLength
  transferFinite windowLength editOffset negativeExtra)

theorem DeletionCode.ConcreteStart.startPositive_correct (k : ℕ) (h : Header) (long : Letters)
    (offset : ℕ) (bits : PartialWords.Bits k) (extra : Bool) (s : Memory)
    (hrho0 : 1 ≤ h.rho) (hrho1 : h.rho ≤ k + 1)
    (hbit : long (editOffset k) = h.bit)
    (hs : Sound s (negativePath k h long) (negativeLength k h))
    (hbound : offset + k ≤ positiveLength k h)
    (hseed : ∀ i : Fin k, positivePath k h long (offset + i.val) = bits i)
    (hextra : h.orientation = .insertion → offset ≤ editOffset k →
      editOffset k < offset + k → extra = negativePath k h long (offset + k - 1)) :
    ∃ t, startPositive k h offset bits extra s = some t ∧
      StartedCorrectly k h long s t := by sorry
