-- Prove2me | Theorems.Thm_Erdos919_rows_bounded
-- name    : Erdos919.rows_bounded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:32:29.740858+00:00
-- url     : https://prove2.me/theorems/bbb46905-3cad-4651-802c-5bb0b0e5c9d2
-- title:
--   Erdos919: rows bounded
-- statement:
--   If a set of order type `< ω₂²` is given, only boundedly many rows meet it unboundedly.
--
--   Source: https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L437-L465
-- source:
--   https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L437-L465

module
public import Mathlib
public import Definitions.Def_Erdos919Palomar_Solution
set_option autoImplicit false
@[expose] public section
public section
universe u
open Cardinal Ordinal Set SimpleGraph
open Erdos919
noncomputable section

theorem Erdos919.rows_bounded (X : Set (W.{u} ×ₗ W.{u})) (hX : typeLT X < typeLT (W.{u} ×ₗ W.{u})) :
    ∃ ξ₀ : W.{u}, ∀ ξ, (∀ x, ∃ η, x ≤ η ∧ toLex (ξ, η) ∈ X) → ξ < ξ₀ := by sorry
