-- Prove2me | Theorems.Thm_F6SmallBlockTokenCapacity_TokenRun_THREE_SITE_CAPACITY
-- name    : F6SmallBlockTokenCapacity.TokenRun.THREE_SITE_CAPACITY
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:31:44.445075+00:00
-- url     : https://prove2.me/theorems/316abd8a-e6b3-5274-abb5-a618f46e7595
-- title:
--   Token Run: THREE SITE CAPACITY
-- statement:
--   Item 6: the forced return contradicts worsening at steps 0 and 2,
--   with the unchanged token at step 1 between them.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6SmallBlockTokenCapacity.lean#L335-L347
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6SmallBlockTokenCapacity.lean#L335-L347

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

theorem F6SmallBlockTokenCapacity.TokenRun.THREE_SITE_CAPACITY (R : TokenRun B W q) (hB : Fintype.card B ≤ 3) :
    q ≤ 2 := by sorry
