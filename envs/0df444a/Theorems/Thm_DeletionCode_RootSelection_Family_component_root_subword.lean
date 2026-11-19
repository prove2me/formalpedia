-- Prove2me | Theorems.Thm_DeletionCode_RootSelection_Family_component_root_subword
-- name    : DeletionCode.RootSelection.Family.component_root_subword
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T04:59:17.394088+00:00
-- url     : https://prove2.me/theorems/97434297-41f1-4007-b069-266a7642fb1b
-- title:
--   Family: component root subword
-- statement:
--   A component root's entire negative word is a genuine contiguous subword of x.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RootSelection.lean#L88-L97
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RootSelection.lean#L88-L97

import Definitions.Def_DeletionCode_WordPaths
import Mathlib.Data.Nat.Find
import Mathlib.Logic.Relation
import Definitions.Def_DeletionCode_RootSelection
set_option autoImplicit true
open DeletionCode DeletionCode.RootSelection
open Windows
open DeletionCode.RootSelection.Family

theorem DeletionCode.RootSelection.Family.component_root_subword {B : Type*} (F : Family B)
    (x : Letters) (n k L : ℕ) (hx : KUnique x n k) (hk : k < L)
    (hgen : F.Generating x n L) (b : B) :
    ∃ r a, F.Connected L r b ∧
      a + (L + F.extra r false) ≤ n ∧
      Agree x a (F.path r false) 0 (L + F.extra r false) := by sorry
