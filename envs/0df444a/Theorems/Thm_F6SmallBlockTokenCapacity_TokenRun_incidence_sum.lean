-- Prove2me | Theorems.Thm_F6SmallBlockTokenCapacity_TokenRun_incidence_sum
-- name    : F6SmallBlockTokenCapacity.TokenRun.incidence_sum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T09:44:48.132666+00:00
-- url     : https://prove2.me/theorems/09694368-501b-5537-b8b5-437eedd8f381
-- title:
--   Token Run: incidence sum
-- statement:
--   Double counting incidences, for any selected set of steps.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6SmallBlockTokenCapacity.lean#L93-L101
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6SmallBlockTokenCapacity.lean#L93-L101

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

theorem F6SmallBlockTokenCapacity.TokenRun.incidence_sum (T : Finset (Fin q)) :
    (∑ i ∈ T, (R.support i).card) =
      ∑ b : B, (T.filter (fun i => b ∈ R.support i)).card := by sorry
