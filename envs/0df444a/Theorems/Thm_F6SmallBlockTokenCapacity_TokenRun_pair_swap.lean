-- Prove2me | Theorems.Thm_F6SmallBlockTokenCapacity_TokenRun_pair_swap
-- name    : F6SmallBlockTokenCapacity.TokenRun.pair_swap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:29:50.95413+00:00
-- url     : https://prove2.me/theorems/89f3f057-2262-454a-a282-decd7535f05c
-- title:
--   Token Run: pair swap
-- statement:
--   A nontrivial transition on a named pair exchanges its two tokens.
--   `hmove` is supplied by HWORSE in a TokenRun; fixing the complement alone
--   would also permit the identity transition.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6SmallBlockTokenCapacity.lean#L200-L218
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6SmallBlockTokenCapacity.lean#L200-L218

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

theorem F6SmallBlockTokenCapacity.TokenRun.pair_swap (s : Finset B) (before after : B ≃ W)
    (hout : ∀ b, b ∉ s → before b = after b)
    (hmove : ∀ b, b ∈ s → before b ≠ after b)
    (x y : B) (_hxy : x ≠ y) (hs : s = {x, y}) :
    after x = before y ∧ after y = before x := by sorry
