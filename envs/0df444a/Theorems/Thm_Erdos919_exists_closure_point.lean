-- Prove2me | Theorems.Thm_Erdos919_exists_closure_point
-- name    : Erdos919.exists_closure_point
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:32:10.409218+00:00
-- url     : https://prove2.me/theorems/50d02660-bd8d-511d-8711-159b81244c41
-- title:
--   Erdos919: exists closure point
-- statement:
--   Closure points of any `β : ω₂ → ω₂` are unbounded.
--
--   Source: https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L389-L411
-- source:
--   https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L389-L411

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

theorem Erdos919.exists_closure_point (β : W.{u} → W.{u}) (a : W.{u}) :
    ∃ δ, a < δ ∧ ∀ ζ < δ, β ζ ≤ δ := by sorry
