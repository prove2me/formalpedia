-- Prove2me | Theorems.Thm_DeletionCode_OverlapCollision_encode_eq_at
-- name    : DeletionCode.OverlapCollision.encode_eq_at
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:40:57.914441+00:00
-- url     : https://prove2.me/theorems/6274f890-f1cc-4bdd-b27c-612951b0d5cd
-- title:
--   Overlap Collision: encode eq at
-- statement:
--   Equality of encodings preserves each bit outside the removed interval.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/OverlapCollision.lean#L36-L49
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/OverlapCollision.lean#L36-L49

import Definitions.Def_DeletionCode_HeaderRecovery
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_OverlapCollision
set_option autoImplicit true
open DeletionCode DeletionCode.OverlapCollision
open Windows HeaderRecovery

theorem DeletionCode.OverlapCollision.encode_eq_at (n k b : ℕ) (hb : b + k ≤ n)
    (x y : Bits n) (heq : encode n k b hb x = encode n k b hb y)
    (j : ℕ) (hj : j < n) (hout : j < b ∨ b + k ≤ j) :
    padBits x j = padBits y j := by sorry
