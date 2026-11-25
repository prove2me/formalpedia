-- Prove2me | Theorems.Thm_F6SmallBlockTokenCapacity_TokenRun_SMALL_BLOCK_TOKEN_CAPACITIES
-- name    : F6SmallBlockTokenCapacity.TokenRun.SMALL_BLOCK_TOKEN_CAPACITIES
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T11:32:29.570805+00:00
-- url     : https://prove2.me/theorems/d3a2d546-12e2-4607-bc73-01a950830e9c
-- title:
--   Token Run: SMALL BLOCK TOKEN CAPACITIES
-- statement:
--   Item 7: both abstract small-block capacities in one theorem.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6SmallBlockTokenCapacity.lean#L350-L352
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6SmallBlockTokenCapacity.lean#L350-L352

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

theorem F6SmallBlockTokenCapacity.TokenRun.SMALL_BLOCK_TOKEN_CAPACITIES (R : TokenRun B W q) :
    (Fintype.card B ≤ 2 → q ≤ 1) ∧ (Fintype.card B ≤ 3 → q ≤ 2) := by sorry
