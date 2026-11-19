-- Prove2me | Theorems.Thm_DeletionCode_RootSelection_Family_component_root_windows
-- name    : DeletionCode.RootSelection.Family.component_root_windows
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T04:59:19.207628+00:00
-- url     : https://prove2.me/theorems/027afb85-62de-4449-a48e-7e00e549164b
-- title:
--   Family: component root windows
-- statement:
--   Every component has a member whose negative windows all occur in x.
--   No rootedness or supplier-closure hypothesis is assumed.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RootSelection.lean#L71-L85
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RootSelection.lean#L71-L85

import Definitions.Def_DeletionCode_WordPaths
import Mathlib.Data.Nat.Find
import Mathlib.Logic.Relation
import Definitions.Def_DeletionCode_RootSelection
set_option autoImplicit true
open DeletionCode DeletionCode.RootSelection
open Windows
open DeletionCode.RootSelection.Family

theorem DeletionCode.RootSelection.Family.component_root_windows {B : Type*} (F : Family B)
    (x : Letters) (n L : ℕ) (hgen : F.Generating x n L) (b : B) :
    ∃ r, F.Connected L r b ∧
      ∀ i, i ≤ F.extra r false → WordPaths.Occurs x n (F.path r false) i L := by sorry
