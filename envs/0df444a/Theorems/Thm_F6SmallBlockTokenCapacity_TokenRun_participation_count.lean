-- Prove2me | Theorems.Thm_F6SmallBlockTokenCapacity_TokenRun_participation_count
-- name    : F6SmallBlockTokenCapacity.TokenRun.participation_count
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T09:32:30.629946+00:00
-- url     : https://prove2.me/theorems/86d3b724-c555-4b09-9259-ae9c3cc14780
-- title:
--   Token Run: participation count
-- statement:
--   Lemma A: post-participation tokens inject into `W` minus the initial token.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6SmallBlockTokenCapacity.lean#L61-L90
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6SmallBlockTokenCapacity.lean#L61-L90

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

theorem F6SmallBlockTokenCapacity.TokenRun.participation_count (b : B) :
    (R.participationSteps b).card ≤ Fintype.card B - 1 := by sorry
