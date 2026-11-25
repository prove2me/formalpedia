-- Prove2me | Theorems.Thm_Erdos919_mk_W
-- name    : Erdos919.mk_W
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:13:00.766376+00:00
-- url     : https://prove2.me/theorems/4a43afae-3e34-5b7a-b9dc-63ac29950fef
-- title:
--   Erdos919: mk W
-- statement:
--   The Erdos919 construction uses the mk W property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L340-L340
-- source:
--   https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L340-L340

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

theorem Erdos919.mk_W : #W.{u} = ℵ_ 2 := by sorry
