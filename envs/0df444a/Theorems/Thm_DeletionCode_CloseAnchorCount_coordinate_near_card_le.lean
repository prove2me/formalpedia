-- Prove2me | Theorems.Thm_DeletionCode_CloseAnchorCount_coordinate_near_card_le
-- name    : DeletionCode.CloseAnchorCount.coordinate_near_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:44:30.835659+00:00
-- url     : https://prove2.me/theorems/8b3772ee-e835-4b4f-8d7f-022b210fd1c5
-- title:
--   Close Anchor Count: coordinate near card le
-- statement:
--   The reference point may depend on every coordinate except the constrained one.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CloseAnchorCount.lean#L79-L92
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CloseAnchorCount.lean#L79-L92

import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Dist
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_DeletionCode_CloseAnchorCount
set_option autoImplicit true
open DeletionCode DeletionCode.CloseAnchorCount
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable

theorem DeletionCode.CloseAnchorCount.coordinate_near_card_le {r n : ℕ} (i : Fin (r + 1))
    (c : (Fin r → Fin n) → ℕ) (B : ℕ) :
    (univ.filter (fun a : Fin (r + 1) → Fin n =>
      Nat.dist (a i).val (c (i.removeNth a)) < B)).card ≤ (2 * B) * n ^ r := by sorry
