-- Prove2me | Theorems.Thm_F6SmallBlockTokenCapacity_TokenRun_previous_holder_mem
-- name    : F6SmallBlockTokenCapacity.TokenRun.previous_holder_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:29:34.643199+00:00
-- url     : https://prove2.me/theorems/c36937f8-57a3-5b9e-8f49-a1287deddb3f
-- title:
--   Token Run: previous holder mem
-- statement:
--   Fixing the complement of a support preserves its pool of previous tokens.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6SmallBlockTokenCapacity.lean#L185-L194
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6SmallBlockTokenCapacity.lean#L185-L194

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
omit [Fintype B] [Fintype W]

theorem F6SmallBlockTokenCapacity.TokenRun.previous_holder_mem (s : Finset B) (before after : B ≃ W)
    (hout : ∀ b, b ∉ s → before b = after b) {x : B} (hx : x ∈ s) :
    before.symm (after x) ∈ s := by sorry
