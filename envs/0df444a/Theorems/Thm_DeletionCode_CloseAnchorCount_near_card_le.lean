-- Prove2me | Theorems.Thm_DeletionCode_CloseAnchorCount_near_card_le
-- name    : DeletionCode.CloseAnchorCount.near_card_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:47:45.329191+00:00
-- url     : https://prove2.me/theorems/8047fbb1-8443-46de-a459-2640de7b26fc
-- title:
--   Close Anchor Count: near card le
-- statement:
--   A natural-number ball, intersected with `Fin n`, contains at most `2 * B` points.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CloseAnchorCount.lean#L32-L51
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CloseAnchorCount.lean#L32-L51

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

theorem DeletionCode.CloseAnchorCount.near_card_le (n c B : ℕ) :
    (univ.filter (fun x : Fin n => Nat.dist x.val c < B)).card ≤ 2 * B := by sorry
