-- Prove2me | Theorems.Thm_DeletionCode_SeedLookup_lookup_eq_some_iff
-- name    : DeletionCode.SeedLookup.lookup_eq_some_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:03:12.127887+00:00
-- url     : https://prove2.me/theorems/b1c91928-a032-485f-bbb8-3b2fac3d5e6f
-- title:
--   Seed Lookup: lookup eq some iff
-- statement:
--   Under k-uniqueness the bounded search returns exactly the matching start.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SeedLookup.lean#L55-L64
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SeedLookup.lean#L55-L64

import Definitions.Def_DeletionCode_Windows
import Mathlib.Data.Fintype.Basic
import Definitions.Def_DeletionCode_SeedLookup
set_option autoImplicit true
open DeletionCode DeletionCode.SeedLookup
open Windows

theorem DeletionCode.SeedLookup.lookup_eq_some_iff (x : Letters) (n k L r a : ℕ) (seed : Fin k → Bool)
    (hx : KUnique x n k) :
    lookup x n k L r seed = some a ↔ Matches x n k L r seed a := by sorry
