-- Prove2me | Theorems.Thm_DeletionCode_OverlapCollision_encode_injective_of_agree
-- name    : DeletionCode.OverlapCollision.encode_injective_of_agree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:40:57.75364+00:00
-- url     : https://prove2.me/theorems/9ed1a93b-36d4-4501-979d-2dff542616d2
-- title:
--   Overlap Collision: encode injective of agree
-- statement:
--   A collision reconstructs each deleted bit from a strictly earlier bit.
--   No disjointness of the two windows is used.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/OverlapCollision.lean#L53-L76
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/OverlapCollision.lean#L53-L76

import Definitions.Def_DeletionCode_HeaderRecovery
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_OverlapCollision
set_option autoImplicit true
open DeletionCode DeletionCode.OverlapCollision
open Windows HeaderRecovery

theorem DeletionCode.OverlapCollision.encode_injective_of_agree (n k a b : ℕ) (hab : a < b)
    (hb : b + k ≤ n) (x y : Bits n)
    (hx : Agree (padBits x) a (padBits x) b k)
    (hy : Agree (padBits y) a (padBits y) b k)
    (heq : encode n k b hb x = encode n k b hb y) : x = y := by sorry
