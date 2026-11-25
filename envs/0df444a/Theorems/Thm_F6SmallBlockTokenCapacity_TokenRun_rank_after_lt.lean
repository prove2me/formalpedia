-- Prove2me | Theorems.Thm_F6SmallBlockTokenCapacity_TokenRun_rank_after_lt
-- name    : F6SmallBlockTokenCapacity.TokenRun.rank_after_lt
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T10:27:51.579881+00:00
-- url     : https://prove2.me/theorems/2aca4dd2-8897-5738-8811-167ee1005703
-- title:
--   Token Run: rank after lt
-- statement:
--   The Token Run construction uses the rank after lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6SmallBlockTokenCapacity.lean#L48-L54
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6SmallBlockTokenCapacity.lean#L48-L54

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

theorem F6SmallBlockTokenCapacity.TokenRun.rank_after_lt (b : B) {i j : Fin q} (hij : i < j)
    (hj : b ∈ R.support j) :
    R.rank b (R.state i.succ b) < R.rank b (R.state j.succ b) := by sorry
