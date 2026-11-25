-- Prove2me | Theorems.Thm_Erdos919_exists_unbounded_fiber
-- name    : Erdos919.exists_unbounded_fiber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:32:15.509896+00:00
-- url     : https://prove2.me/theorems/40e72aa6-e4b8-59e9-b646-2f25faa099eb
-- title:
--   Erdos919: exists unbounded fiber
-- statement:
--   Every colouring of `ω₂` with at most `ℵ₁` colours has an unbounded colour class.
--
--   Source: https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L380-L386
-- source:
--   https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L380-L386

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

theorem Erdos919.exists_unbounded_fiber {α : Type u} (hα : #α ≤ ℵ₁) (d : W.{u} → α) :
    ∃ a, ∀ x, ∃ y, x ≤ y ∧ d y = a := by sorry
