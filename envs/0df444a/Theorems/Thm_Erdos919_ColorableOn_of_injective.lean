-- Prove2me | Theorems.Thm_Erdos919_ColorableOn_of_injective
-- name    : Erdos919.ColorableOn.of_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:30:11.326392+00:00
-- url     : https://prove2.me/theorems/e594bec6-c78e-53bd-ab00-fae83195ba95
-- title:
--   Colorable On: of injective
-- statement:
--   The Colorable On construction uses the of injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L69-L72
-- source:
--   https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L69-L72

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

theorem Erdos919.ColorableOn.of_injective {V : Type*} {G : SimpleGraph V} {X : Set V} {α β : Type*}
    (h : ColorableOn G X α) (f : α → β) (hf : Function.Injective f) : ColorableOn G X β := by sorry
