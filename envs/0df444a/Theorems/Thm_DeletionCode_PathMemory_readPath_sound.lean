-- Prove2me | Theorems.Thm_DeletionCode_PathMemory_readPath_sound
-- name    : DeletionCode.PathMemory.readPath_sound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:13:35.210081+00:00
-- url     : https://prove2.me/theorems/afce090f-aea9-40b4-a9b2-e363bd27a30f
-- title:
--   Path Memory: read Path sound
-- statement:
--   The Path Memory construction uses the read Path sound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/PathMemory.lean#L55-L90
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/PathMemory.lean#L55-L90

import Definitions.Def_DeletionCode_HeaderRecovery
import Definitions.Def_DeletionCode_PartialWords
import Definitions.Def_DeletionCode_SelectedWindows
import Definitions.Def_DeletionCode_PathMemory
set_option autoImplicit true
open DeletionCode DeletionCode.PathMemory
open Windows HeaderRecovery PartialWords SelectedWindows

theorem DeletionCode.PathMemory.readPath_sound (k : ℕ) (h : Header) (long : Letters) (s : Memory)
    (side : Bool) (start len : ℕ) (bits : PartialWords.Bits len)
    (hrho0 : 1 ≤ h.rho) (hrho1 : h.rho ≤ k + 1)
    (hbit : long (editOffset k) = h.bit)
    (hs : Sound s (negativePath k h long) (negativeLength k h))
    (hread : readPath k h s side start len = some bits) :
    Matches bits (pathLetters k h long side) start := by sorry
