-- Prove2me | Theorems.Thm_F6SmallBlockTokenCapacity_TokenRun_SIX_SITE_INCIDENCE_OPTIONAL
-- name    : F6SmallBlockTokenCapacity.TokenRun.SIX_SITE_INCIDENCE_OPTIONAL
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T11:34:06.772135+00:00
-- url     : https://prove2.me/theorems/291a2b6a-7ba8-4b57-8aa6-7df25a02ceef
-- title:
--   Token Run: SIX SITE INCIDENCE OPTIONAL
-- statement:
--   OPTIONAL item 8: the generic six-site incidence consequence.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6SmallBlockTokenCapacity.lean#L355-L360
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6SmallBlockTokenCapacity.lean#L355-L360

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

theorem F6SmallBlockTokenCapacity.TokenRun.SIX_SITE_INCIDENCE_OPTIONAL (R : TokenRun B W q) (hB : Fintype.card B ≤ 6) :
    2 * q ≤ 6 * 5 ∧ q ≤ 15 := by sorry
