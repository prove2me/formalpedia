-- Prove2me | Theorems.Thm_F6SmallBlockTokenCapacity_TokenRun_incidence_bounds
-- name    : F6SmallBlockTokenCapacity.TokenRun.incidence_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:45:07.86159+00:00
-- url     : https://prove2.me/theorems/e34ff9d2-f474-4c24-89e1-a5e2986d78fd
-- title:
--   Token Run: incidence bounds
-- statement:
--   The two sides of the incidence squeeze used in the frozen proof.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6SmallBlockTokenCapacity.lean#L120-L131
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6SmallBlockTokenCapacity.lean#L120-L131

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

theorem F6SmallBlockTokenCapacity.TokenRun.incidence_bounds :
    2 * q ≤ (∑ i : Fin q, (R.support i).card) ∧
    (∑ i : Fin q, (R.support i).card) ≤ Fintype.card B * (Fintype.card B - 1) := by sorry
