-- Prove2me | Theorems.Thm_F6SmallBlockTokenCapacity_TokenRun_three_membership_sum
-- name    : F6SmallBlockTokenCapacity.TokenRun.three_membership_sum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T10:30:39.884681+00:00
-- url     : https://prove2.me/theorems/9d7088e2-7cdc-5198-b3f9-e91e505bf693
-- title:
--   Token Run: three membership sum
-- statement:
--   Expanding the three index positions is just a representation lemma.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6SmallBlockTokenCapacity.lean#L253-L259
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6SmallBlockTokenCapacity.lean#L253-L259

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
omit [Fintype B]

theorem F6SmallBlockTokenCapacity.TokenRun.three_membership_sum (S : Fin 3 → Finset B) (b : B) :
    ((Finset.univ : Finset (Fin 3)).filter (fun i => b ∈ S i)).card =
      (if b ∈ S 0 then 1 else 0) + (if b ∈ S 1 then 1 else 0) +
        (if b ∈ S 2 then 1 else 0) := by sorry
