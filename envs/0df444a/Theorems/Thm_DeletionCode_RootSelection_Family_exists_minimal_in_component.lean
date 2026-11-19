-- Prove2me | Theorems.Thm_DeletionCode_RootSelection_Family_exists_minimal_in_component
-- name    : DeletionCode.RootSelection.Family.exists_minimal_in_component
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T04:59:01.114549+00:00
-- url     : https://prove2.me/theorems/8671d378-5d10-4a93-a8f1-d902a1bf35f7
-- title:
--   Family: exists minimal in component
-- statement:
--   Natural-number rank has a least value in every nonempty component.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RootSelection.lean#L57-L67
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RootSelection.lean#L57-L67

import Definitions.Def_DeletionCode_WordPaths
import Mathlib.Data.Nat.Find
import Mathlib.Logic.Relation
import Definitions.Def_DeletionCode_RootSelection
set_option autoImplicit true
open DeletionCode DeletionCode.RootSelection
open Windows
open DeletionCode.RootSelection.Family

theorem DeletionCode.RootSelection.Family.exists_minimal_in_component {B : Type*} (F : Family B) (L : ℕ) (b : B) :
    ∃ r, F.Connected L r b ∧
      ∀ a, F.Connected L a b → F.rank r ≤ F.rank a := by sorry
