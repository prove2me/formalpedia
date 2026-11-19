-- Prove2me | Theorems.Thm_DeletionCode_SeedLookup_matches_unique
-- name    : DeletionCode.SeedLookup.matches_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:02:58.413685+00:00
-- url     : https://prove2.me/theorems/af0242e6-5a9f-4cb5-ab86-c806ae9b0d85
-- title:
--   Seed Lookup: matches unique
-- statement:
--   The Seed Lookup construction uses the matches unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SeedLookup.lean#L47-L52
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SeedLookup.lean#L47-L52

import Definitions.Def_DeletionCode_Windows
import Mathlib.Data.Fintype.Basic
import Definitions.Def_DeletionCode_SeedLookup
set_option autoImplicit true
open DeletionCode DeletionCode.SeedLookup
open Windows

theorem DeletionCode.SeedLookup.matches_unique (x : Letters) (n k L r a b : ℕ) (seed : Fin k → Bool)
    (hx : KUnique x n k) (ha : Matches x n k L r seed a)
    (hb : Matches x n k L r seed b) : a = b := by sorry
