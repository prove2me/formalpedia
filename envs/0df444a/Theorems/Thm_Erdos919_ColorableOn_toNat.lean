-- Prove2me | Theorems.Thm_Erdos919_ColorableOn_toNat
-- name    : Erdos919.ColorableOn.toNat
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T18:18:52.322801+00:00
-- url     : https://prove2.me/theorems/a1e08a83-2a94-57a8-bf2e-0de6f7bc7e1e
-- title:
--   Colorable On: to Nat
-- statement:
--   The Colorable On construction uses the to Nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L74-L76
-- source:
--   https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L74-L76

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

theorem Erdos919.ColorableOn.toNat {V : Type*} {G : SimpleGraph V} {X : Set V} {β : Type*}
    [Encodable β] (h : ColorableOn G X β) : ColorableOn G X ℕ := by sorry
