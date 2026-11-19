-- Prove2me | Theorems.Thm_DeletionCode_CloseAnchorCount_bad_card_le
-- name    : DeletionCode.CloseAnchorCount.bad_card_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:44:46.549496+00:00
-- url     : https://prove2.me/theorems/30ef4a11-34f6-48e7-ab2b-f9f55ff7c784
-- title:
--   Close Anchor Count: bad card le
-- statement:
--   A union bound over all actual endpoint and pair constraints. The exponent
--   is `r - 1`, and the theorem also covers `r = 0`, `n = 0`, and `B = 0`.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CloseAnchorCount.lean#L143-L173
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CloseAnchorCount.lean#L143-L173

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

theorem DeletionCode.CloseAnchorCount.bad_card_le (r n m B : ℕ) :
    (univ.filter (Bad (r := r) (n := n) m B)).card ≤
      r * (r + 2) * (2 * B) * n ^ (r - 1) := by sorry
