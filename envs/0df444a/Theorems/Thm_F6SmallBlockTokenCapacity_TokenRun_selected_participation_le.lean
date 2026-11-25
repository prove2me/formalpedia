-- Prove2me | Theorems.Thm_F6SmallBlockTokenCapacity_TokenRun_selected_participation_le
-- name    : F6SmallBlockTokenCapacity.TokenRun.selected_participation_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T11:24:32.05191+00:00
-- url     : https://prove2.me/theorems/22a214d2-fe00-4b5d-a413-def92a8bf6a1
-- title:
--   Token Run: selected participation le
-- statement:
--   The Token Run construction uses the selected participation le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6SmallBlockTokenCapacity.lean#L103-L108
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6SmallBlockTokenCapacity.lean#L103-L108

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

theorem F6SmallBlockTokenCapacity.TokenRun.selected_participation_le (T : Finset (Fin q)) (b : B) :
    (T.filter (fun i => b ∈ R.support i)).card ≤ Fintype.card B - 1 := by sorry
