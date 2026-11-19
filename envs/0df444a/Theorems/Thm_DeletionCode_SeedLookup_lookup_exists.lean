-- Prove2me | Theorems.Thm_DeletionCode_SeedLookup_lookup_exists
-- name    : DeletionCode.SeedLookup.lookup_exists
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:02:59.051346+00:00
-- url     : https://prove2.me/theorems/257760aa-bd49-4e12-b322-ddf44b7dc4e0
-- title:
--   Seed Lookup: lookup exists
-- statement:
--   The Seed Lookup construction uses the lookup exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SeedLookup.lean#L32-L45
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SeedLookup.lean#L32-L45

import Definitions.Def_DeletionCode_Windows
import Mathlib.Data.Fintype.Basic
import Definitions.Def_DeletionCode_SeedLookup
set_option autoImplicit true
open DeletionCode DeletionCode.SeedLookup
open Windows

theorem DeletionCode.SeedLookup.lookup_exists (x : Letters) (n k L r : ℕ) (seed : Fin k → Bool)
    (h : ∃ a, Matches x n k L r seed a) :
    ∃ a, lookup x n k L r seed = some a := by sorry
