-- Prove2me | Theorems.Thm_Erdos919_colorableOn_iff_induce
-- name    : Erdos919.colorableOn_iff_induce
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:29:25.186385+00:00
-- url     : https://prove2.me/theorems/83ab8c8e-0e87-47fd-bfb7-0203127aadbd
-- title:
--   Erdos919: colorable On iff induce
-- statement:
--   `ColorableOn` is the same as colourability of the induced subgraph.
--
--   Source: https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L52-L62
-- source:
--   https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L52-L62

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

theorem Erdos919.colorableOn_iff_induce {V : Type*} (G : SimpleGraph V) (X : Set V) (α : Type*)
    [Nonempty α] : ColorableOn G X α ↔ Nonempty ((G.induce X).Coloring α) := by sorry
