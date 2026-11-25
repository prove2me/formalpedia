-- Prove2me | Theorems.Thm_F6SmallBlockTokenCapacity_TokenRun_THREE_STEP_RETURN
-- name    : F6SmallBlockTokenCapacity.TokenRun.THREE_STEP_RETURN
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T10:31:58.153088+00:00
-- url     : https://prove2.me/theorems/f57b616f-71b8-4a16-b94a-c4938e56a891
-- title:
--   Token Run: THREE STEP RETURN
-- statement:
--   Item 5: the three swaps along the triangle return `x` to its initial token.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6SmallBlockTokenCapacity.lean#L315-L331
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6SmallBlockTokenCapacity.lean#L315-L331

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

theorem F6SmallBlockTokenCapacity.TokenRun.THREE_STEP_RETURN (P : TokenRun B W 3)
    (hB : Fintype.card B = 3)
    (hs : ∀ i, (P.support i).card = 2)
    (hc : ∀ b : B, (P.participationSteps b).card = 2) :
    ∃ x : B, x ∈ P.support 0 ∧ x ∉ P.support 1 ∧ x ∈ P.support 2 ∧
      P.state 3 x = P.state 0 x := by sorry
