-- Prove2me | Theorems.Thm_F6SmallBlockTokenCapacity_TokenRun_pair_of_card_two_mem
-- name    : F6SmallBlockTokenCapacity.TokenRun.pair_of_card_two_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:30:05.05196+00:00
-- url     : https://prove2.me/theorems/4fd25fe4-c281-422c-a8c4-af3cc03765e0
-- title:
--   Token Run: pair of card two mem
-- statement:
--   A representation lemma naming the other member of a pair.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6SmallBlockTokenCapacity.lean#L242-L249
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6SmallBlockTokenCapacity.lean#L242-L249

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
omit [Fintype B]

theorem F6SmallBlockTokenCapacity.TokenRun.pair_of_card_two_mem (s : Finset B) (hs : s.card = 2) (x : B) (hx : x ∈ s) :
    ∃ a : B, x ≠ a ∧ s = {x, a} := by sorry
