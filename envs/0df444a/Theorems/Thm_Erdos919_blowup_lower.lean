-- Prove2me | Theorems.Thm_Erdos919_blowup_lower
-- name    : Erdos919.blowup_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:30:47.494227+00:00
-- url     : https://prove2.me/theorems/eb2c0536-4557-4a3c-b380-4d24b016b905
-- title:
--   Erdos919: blowup lower
-- statement:
--   Lower bound: if every `α`-colouring of a row has a colour class that is unbounded, then an
--   `α`-colouring of `blowup H` yields an `α`-colouring of `H`.
--
--   Source: https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L113-L130
-- source:
--   https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L113-L130

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
variable {I : Type*} [LinearOrder I]

theorem Erdos919.blowup_lower {H : SimpleGraph I} {α : Type*}
    (hfib : ∀ d : I → α, ∃ a, ∀ x, ∃ y, x ≤ y ∧ d y = a)
    (c : (blowup H).Coloring α) : Nonempty (H.Coloring α) := by sorry
