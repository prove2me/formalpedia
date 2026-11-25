-- Prove2me | Theorems.Thm_Erdos919_bigGraph_lower
-- name    : Erdos919.bigGraph_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:23:29.296113+00:00
-- url     : https://prove2.me/theorems/96731a27-9810-57a2-a0fb-ee3a7f318c0e
-- title:
--   Erdos919: big Graph lower
-- statement:
--   The Erdos919 construction uses the big Graph lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L528-L530
-- source:
--   https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L528-L530

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

theorem Erdos919.bigGraph_lower {H : SimpleGraph W.{u}} {α : Type u} (hα : #α ≤ ℵ₁)
    (c : (bigGraph H).Coloring α) : Nonempty (H.Coloring α) := by sorry
