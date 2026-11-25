-- Prove2me | Theorems.Thm_Erdos919_ColorableOn_mono_set
-- name    : Erdos919.ColorableOn.mono_set
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:18:44.511237+00:00
-- url     : https://prove2.me/theorems/86e2b320-622f-5bd9-81f5-376469dc0aa5
-- title:
--   Colorable On: mono set
-- statement:
--   The Colorable On construction uses the mono set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L64-L67
-- source:
--   https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L64-L67

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

theorem Erdos919.ColorableOn.mono_set {V : Type*} {G : SimpleGraph V} {X Y : Set V} {α : Type*}
    (h : ColorableOn G Y α) (hXY : X ⊆ Y) : ColorableOn G X α := by sorry
