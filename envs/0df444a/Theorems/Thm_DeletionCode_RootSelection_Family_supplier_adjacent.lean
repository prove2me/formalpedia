-- Prove2me | Theorems.Thm_DeletionCode_RootSelection_Family_supplier_adjacent
-- name    : DeletionCode.RootSelection.Family.supplier_adjacent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T04:59:00.931916+00:00
-- url     : https://prove2.me/theorems/4459b8d7-1652-455d-a0e6-86b5ce65e347
-- title:
--   Family: supplier adjacent
-- statement:
--   Sharing an entire valid gram also gives a common de Bruijn vertex.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RootSelection.lean#L47-L54
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RootSelection.lean#L47-L54

import Definitions.Def_DeletionCode_WordPaths
import Mathlib.Data.Nat.Find
import Mathlib.Logic.Relation
import Definitions.Def_DeletionCode_RootSelection
set_option autoImplicit true
open DeletionCode DeletionCode.RootSelection
open Windows
open DeletionCode.RootSelection.Family

theorem DeletionCode.RootSelection.Family.supplier_adjacent {B : Type*} (F : Family B) (L : ℕ)
    (b a : B) (side : Bool) (i j : ℕ)
    (hi : i ≤ F.extra b false) (hj : j ≤ F.extra a side)
    (hgram : Agree (F.path b false) i (F.path a side) j L) :
    F.Adjacent L b a := by sorry
