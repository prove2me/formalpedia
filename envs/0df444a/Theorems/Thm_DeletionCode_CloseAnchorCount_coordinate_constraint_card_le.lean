-- Prove2me | Theorems.Thm_DeletionCode_CloseAnchorCount_coordinate_constraint_card_le
-- name    : DeletionCode.CloseAnchorCount.coordinate_constraint_card_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:47:44.484668+00:00
-- url     : https://prove2.me/theorems/cc464b2c-7a83-4d87-b439-1d0ffc99b17b
-- title:
--   Close Anchor Count: coordinate constraint card le
-- statement:
--   Omitting one coordinate leaves exactly `n^r` possible records; each record
--   admits at most `M` values of the omitted coordinate.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CloseAnchorCount.lean#L55-L76
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CloseAnchorCount.lean#L55-L76

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

theorem DeletionCode.CloseAnchorCount.coordinate_constraint_card_le {r n : ℕ} (i : Fin (r + 1))
    (P : (Fin r → Fin n) → Fin n → Prop) (M : ℕ)
    (hM : ∀ b, (univ.filter (P b)).card ≤ M) :
    (univ.filter (fun a : Fin (r + 1) → Fin n => P (i.removeNth a) (a i))).card ≤
      M * n ^ r := by sorry
