-- Prove2me | Theorems.Thm_F6SmallBlockTokenCapacity_TokenRun_THREE_SITE_INCIDENCE_EQUALITY
-- name    : F6SmallBlockTokenCapacity.TokenRun.THREE_SITE_INCIDENCE_EQUALITY
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:29:23.230621+00:00
-- url     : https://prove2.me/theorems/aa095462-25c0-5508-a313-b235b99a0e4f
-- title:
--   Token Run: THREE SITE INCIDENCE EQUALITY
-- statement:
--   Item 3, stated for the first three steps of an arbitrary-length run.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6SmallBlockTokenCapacity.lean#L177-L181
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6SmallBlockTokenCapacity.lean#L177-L181

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

theorem F6SmallBlockTokenCapacity.TokenRun.THREE_SITE_INCIDENCE_EQUALITY (hB : Fintype.card B ≤ 3) (hq : 3 ≤ q) :
    Fintype.card B = 3 ∧
    (∀ i : Fin 3, ((R.firstSteps 3 hq).support i).card = 2) ∧
    (∀ b : B, ((R.firstSteps 3 hq).participationSteps b).card = 2) := by sorry
