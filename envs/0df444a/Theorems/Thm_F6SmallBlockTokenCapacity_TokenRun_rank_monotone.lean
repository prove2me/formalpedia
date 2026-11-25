-- Prove2me | Theorems.Thm_F6SmallBlockTokenCapacity_TokenRun_rank_monotone
-- name    : F6SmallBlockTokenCapacity.TokenRun.rank_monotone
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T09:41:25.53781+00:00
-- url     : https://prove2.me/theorems/9bb1b28a-e8d6-5a7b-a10c-9a7b8c416f9f
-- title:
--   Token Run: rank monotone
-- statement:
--   Ranks never decrease, including the transitions outside the support.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6SmallBlockTokenCapacity.lean#L40-L46
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6SmallBlockTokenCapacity.lean#L40-L46

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

theorem F6SmallBlockTokenCapacity.TokenRun.rank_monotone (b : B) : Monotone (fun t => R.rank b (R.state t b)) := by sorry
