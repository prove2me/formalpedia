-- Prove2me | Theorems.Thm_F6SmallBlockTokenCapacity_TokenRun_named_pair_swap
-- name    : F6SmallBlockTokenCapacity.TokenRun.named_pair_swap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:44:56.043632+00:00
-- url     : https://prove2.me/theorems/bedd02a4-e14c-5307-bd8c-48689fec1f66
-- title:
--   Token Run: named pair swap
-- statement:
--   The Token Run construction uses the named pair swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6SmallBlockTokenCapacity.lean#L220-L229
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6SmallBlockTokenCapacity.lean#L220-L229

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

theorem F6SmallBlockTokenCapacity.TokenRun.named_pair_swap (i : Fin q) (x y : B) (hxy : x ≠ y)
    (hs : R.support i = {x, y}) :
    R.state i.succ x = R.state i.castSucc y ∧
    R.state i.succ y = R.state i.castSucc x := by sorry
