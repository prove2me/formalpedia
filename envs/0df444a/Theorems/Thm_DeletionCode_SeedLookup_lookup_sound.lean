-- Prove2me | Theorems.Thm_DeletionCode_SeedLookup_lookup_sound
-- name    : DeletionCode.SeedLookup.lookup_sound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:00:22.950649+00:00
-- url     : https://prove2.me/theorems/4ee418f2-db96-492b-bdaf-810ed9856a70
-- title:
--   Seed Lookup: lookup sound
-- statement:
--   The Seed Lookup construction uses the lookup sound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SeedLookup.lean#L26-L30
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SeedLookup.lean#L26-L30

import Definitions.Def_DeletionCode_Windows
import Mathlib.Data.Fintype.Basic
import Definitions.Def_DeletionCode_SeedLookup
set_option autoImplicit true
open DeletionCode DeletionCode.SeedLookup
open Windows

theorem DeletionCode.SeedLookup.lookup_sound (x : Letters) (n k L r a : ℕ) (seed : Fin k → Bool)
    (h : lookup x n k L r seed = some a) : Matches x n k L r seed a := by sorry
