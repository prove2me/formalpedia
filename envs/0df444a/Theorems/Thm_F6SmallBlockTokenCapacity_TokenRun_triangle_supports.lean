-- Prove2me | Theorems.Thm_F6SmallBlockTokenCapacity_TokenRun_triangle_supports
-- name    : F6SmallBlockTokenCapacity.TokenRun.triangle_supports
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:30:43.609797+00:00
-- url     : https://prove2.me/theorems/916d3588-9d38-59c4-8816-5c5d24fc1c7c
-- title:
--   Token Run: triangle supports
-- statement:
--   The equality structure forces the frozen triangle of supports.
--   This is a set-cardinality argument, without enumerating states or permutations.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6SmallBlockTokenCapacity.lean#L263-L312
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6SmallBlockTokenCapacity.lean#L263-L312

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

theorem F6SmallBlockTokenCapacity.TokenRun.triangle_supports (S : Fin 3 → Finset B) (hB : Fintype.card B = 3)
    (hs : ∀ i, (S i).card = 2)
    (hc : ∀ b : B,
      ((Finset.univ : Finset (Fin 3)).filter (fun i => b ∈ S i)).card = 2) :
    ∃ x a b : B, x ≠ a ∧ x ≠ b ∧ a ≠ b ∧
      S 0 = {x, a} ∧ S 1 = {a, b} ∧ S 2 = {x, b} := by sorry
