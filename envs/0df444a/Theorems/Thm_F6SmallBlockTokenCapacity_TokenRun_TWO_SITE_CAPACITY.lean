-- Prove2me | Theorems.Thm_F6SmallBlockTokenCapacity_TokenRun_TWO_SITE_CAPACITY
-- name    : F6SmallBlockTokenCapacity.TokenRun.TWO_SITE_CAPACITY
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T10:28:55.419173+00:00
-- url     : https://prove2.me/theorems/663aad25-9281-4d78-8cf6-e293bc02a979
-- title:
--   Token Run: TWO SITE CAPACITY
-- statement:
--   Two supports in a two-site run would both be the entire site type.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6SmallBlockTokenCapacity.lean#L134-L148
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6SmallBlockTokenCapacity.lean#L134-L148

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

theorem F6SmallBlockTokenCapacity.TokenRun.TWO_SITE_CAPACITY (R : TokenRun B W q) (hB : Fintype.card B ≤ 2) : q ≤ 1 := by sorry
