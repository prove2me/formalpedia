-- Prove2me | Theorems.Thm_DeletionCode_OverlapCollision_collision_card_le
-- name    : DeletionCode.OverlapCollision.collision_card_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:41:09.606774+00:00
-- url     : https://prove2.me/theorems/73b70d47-8569-4672-832e-727988a56724
-- title:
--   Overlap Collision: collision card le
-- statement:
--   The concrete collision set has at most 2^(n-k) members, even when the
--   windows overlap. The earlier window bound follows already from a<b and hb.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/OverlapCollision.lean#L90-L97
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/OverlapCollision.lean#L90-L97

import Definitions.Def_DeletionCode_HeaderRecovery
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_OverlapCollision
set_option autoImplicit true
open DeletionCode DeletionCode.OverlapCollision
open Windows HeaderRecovery

theorem DeletionCode.OverlapCollision.collision_card_le (n k a b : ℕ) (hab : a < b)
    (_ha : a + k ≤ n) (hb : b + k ≤ n) :
    Fintype.card (Collision n k a b) ≤ 2 ^ (n - k) := by sorry
