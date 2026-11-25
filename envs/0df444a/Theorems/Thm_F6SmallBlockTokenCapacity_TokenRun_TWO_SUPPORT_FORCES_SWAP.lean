-- Prove2me | Theorems.Thm_F6SmallBlockTokenCapacity_TokenRun_TWO_SUPPORT_FORCES_SWAP
-- name    : F6SmallBlockTokenCapacity.TokenRun.TWO_SUPPORT_FORCES_SWAP
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T11:28:18.199744+00:00
-- url     : https://prove2.me/theorems/33abfe18-349f-4cc8-b84f-b4784b195b2e
-- title:
--   Token Run: TWO SUPPORT FORCES SWAP
-- statement:
--   Item 4: the two members of a two-element support exchange their tokens.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6SmallBlockTokenCapacity.lean#L232-L238
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6SmallBlockTokenCapacity.lean#L232-L238

import Mathlib
import Definitions.Def_StableMarriageF6_F6SmallBlockTokenCapacity
set_option autoImplicit true
open scoped BigOperators
open Classical
noncomputable section
open F6SmallBlockTokenCapacity
variable {B W : Type*} [Fintype B] [Fintype W] {q : ℕ}
open F6SmallBlockTokenCapacity.TokenRun
variable (R : TokenRun B W q)

theorem F6SmallBlockTokenCapacity.TokenRun.TWO_SUPPORT_FORCES_SWAP (i : Fin q) (hcard : (R.support i).card = 2) :
    ∃ x y : B, x ≠ y ∧ R.support i = {x, y} ∧
      R.state i.succ x = R.state i.castSucc y ∧
      R.state i.succ y = R.state i.castSucc x := by sorry
