-- Prove2me | Theorems.Thm_DeletionCode_SeedLookup_recoverWindow_sound
-- name    : DeletionCode.SeedLookup.recoverWindow_sound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:11:59.803266+00:00
-- url     : https://prove2.me/theorems/bb2b2658-a23a-4b7d-a407-fb7779f74280
-- title:
--   Seed Lookup: recover Window sound
-- statement:
--   Any returned window really is an in-bounds window of the fixed word.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SeedLookup.lean#L72-L80
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SeedLookup.lean#L72-L80

import Definitions.Def_DeletionCode_Windows
import Mathlib.Data.Fintype.Basic
import Definitions.Def_DeletionCode_SeedLookup
set_option autoImplicit true
open DeletionCode DeletionCode.SeedLookup
open Windows

theorem DeletionCode.SeedLookup.recoverWindow_sound (x : Letters) (n k L r : ℕ) (seed : Fin k → Bool)
    (bits : Fin L → Bool) (h : recoverWindow x n k L r seed = some bits) :
    ∃ a, Matches x n k L r seed a ∧ bits = fun i => x (a + i.val) := by sorry
