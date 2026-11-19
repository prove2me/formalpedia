-- Prove2me | Theorems.Thm_DeletionCode_SeedLookup_recoverWindow_of_occurrence
-- name    : DeletionCode.SeedLookup.recoverWindow_of_occurrence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:12:03.763199+00:00
-- url     : https://prove2.me/theorems/7e8deb88-0a19-4b62-8f11-06875e390e73
-- title:
--   Seed Lookup: recover Window of occurrence
-- statement:
--   A target window occurring in x is recovered exactly from its seed.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SeedLookup.lean#L83-L102
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SeedLookup.lean#L83-L102

import Definitions.Def_DeletionCode_Windows
import Mathlib.Data.Fintype.Basic
import Definitions.Def_DeletionCode_SeedLookup
set_option autoImplicit true
open DeletionCode DeletionCode.SeedLookup
open Windows

theorem DeletionCode.SeedLookup.recoverWindow_of_occurrence
    (x target : Letters) (n k L r a w : ℕ) (seed : Fin k → Bool)
    (hx : KUnique x n k) (hr : r + k ≤ L) (ha : a + L ≤ n)
    (hocc : Agree x a target w L)
    (hseed : ∀ i : Fin k, seed i = target (w + r + i.val)) :
    recoverWindow x n k L r seed = some (fun i : Fin L => target (w + i.val)) := by sorry
