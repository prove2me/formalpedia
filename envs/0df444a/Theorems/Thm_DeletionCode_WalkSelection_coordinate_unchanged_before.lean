-- Prove2me | Theorems.Thm_DeletionCode_WalkSelection_coordinate_unchanged_before
-- name    : DeletionCode.WalkSelection.coordinate_unchanged_before
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:14:16.175165+00:00
-- url     : https://prove2.me/theorems/764fe608-b034-4ce6-b8c0-5bf827626a1e
-- title:
--   Walk Selection: coordinate unchanged before
-- statement:
--   A coordinate unchanged by all earlier actual steps has its starting value.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WalkSelection.lean#L146-L157
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WalkSelection.lean#L146-L157

import Definitions.Def_DeletionCode_ClosedWalk
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Definitions.Def_DeletionCode_WalkSelection
set_option autoImplicit true
open DeletionCode DeletionCode.WalkSelection
open scoped BigOperators
variable {V : Type*} [AddCommGroup V] [Module ℚ V] {m : ℕ}

theorem DeletionCode.WalkSelection.coordinate_unchanged_before {H : Type*} (p : Fin (m + 1) → H → ℚ)
    (n : ℕ) (hn : n ≤ m) (h : H)
    (hzero : ∀ j : Fin m, j.val < n → walkStep p j h = 0) :
    p ⟨n, by omega⟩ h = p 0 h := by sorry
