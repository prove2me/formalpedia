-- Prove2me | Theorems.Thm_F6SmallBlockTokenCapacity_TokenRun_initial_rank_lt_after
-- name    : F6SmallBlockTokenCapacity.TokenRun.initial_rank_lt_after
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:28:06.305341+00:00
-- url     : https://prove2.me/theorems/63e6fd21-a5f5-591d-aef4-f35bcdeda41d
-- title:
--   Token Run: initial rank lt after
-- statement:
--   The Token Run construction uses the initial rank lt after property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6SmallBlockTokenCapacity.lean#L56-L58
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6SmallBlockTokenCapacity.lean#L56-L58

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

theorem F6SmallBlockTokenCapacity.TokenRun.initial_rank_lt_after (b : B) {i : Fin q} (hi : b ∈ R.support i) :
    R.rank b (R.state 0 b) < R.rank b (R.state i.succ b) := by sorry
