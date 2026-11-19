-- Prove2me | Theorems.Thm_DeletionCode_PathMemory_readPath_complete
-- name    : DeletionCode.PathMemory.readPath_complete
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:13:46.676213+00:00
-- url     : https://prove2.me/theorems/4a639844-6893-4081-b4d3-9736f37f68a7
-- title:
--   Path Memory: read Path complete
-- statement:
--   Completed sound negative memory supplies correct data on either path.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/PathMemory.lean#L111-L122
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/PathMemory.lean#L111-L122

import Definitions.Def_DeletionCode_HeaderRecovery
import Definitions.Def_DeletionCode_PartialWords
import Definitions.Def_DeletionCode_SelectedWindows
import Definitions.Def_DeletionCode_PathMemory
set_option autoImplicit true
open DeletionCode DeletionCode.PathMemory
open Windows HeaderRecovery PartialWords SelectedWindows

theorem DeletionCode.PathMemory.readPath_complete (k : ℕ) (h : Header) (long : Letters) (s : Memory)
    (side : Bool) (start len : ℕ)
    (hrho0 : 1 ≤ h.rho) (hrho1 : h.rho ≤ k + 1)
    (hbit : long (editOffset k) = h.bit)
    (hs : Sound s (negativePath k h long) (negativeLength k h))
    (hknown : WindowKnown s 0 (negativeLength k h))
    (hbound : start + len ≤ pathLength k h side) :
    ∃ bits, readPath k h s side start len = some bits ∧
      Matches bits (pathLetters k h long side) start := by sorry
