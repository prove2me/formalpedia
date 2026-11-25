-- Prove2me | Theorems.Thm_F6SmallBlockTokenCapacity_TokenRun_mem_participationSteps
-- name    : F6SmallBlockTokenCapacity.TokenRun.mem_participationSteps
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:31:09.511543+00:00
-- url     : https://prove2.me/theorems/ddd23a2e-e05e-5418-9c1d-a1cab833dec5
-- title:
--   Token Run: mem participation Steps
-- statement:
--   The Token Run construction uses the mem participation Steps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6SmallBlockTokenCapacity.lean#L34-L37
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6SmallBlockTokenCapacity.lean#L34-L37

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

theorem F6SmallBlockTokenCapacity.TokenRun.mem_participationSteps (b : B) (i : Fin q) :
    i ∈ R.participationSteps b ↔ b ∈ R.support i := by sorry
