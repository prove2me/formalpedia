-- Prove2me | Theorems.Thm_DeletionCode_OverlapCollision_collisionEncode_injective
-- name    : DeletionCode.OverlapCollision.collisionEncode_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:41:02.337254+00:00
-- url     : https://prove2.me/theorems/6cf75f84-55e4-452f-bfe0-20618abfb922
-- title:
--   Overlap Collision: collision Encode injective
-- statement:
--   The Overlap Collision construction uses the collision Encode injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/OverlapCollision.lean#L82-L86
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/OverlapCollision.lean#L82-L86

import Definitions.Def_DeletionCode_HeaderRecovery
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_OverlapCollision
set_option autoImplicit true
open DeletionCode DeletionCode.OverlapCollision
open Windows HeaderRecovery

theorem DeletionCode.OverlapCollision.collisionEncode_injective (n k a b : ℕ) (hab : a < b)
    (hb : b + k ≤ n) : Function.Injective (collisionEncode n k a b hb) := by sorry
