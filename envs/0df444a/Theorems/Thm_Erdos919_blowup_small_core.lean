-- Prove2me | Theorems.Thm_Erdos919_blowup_small_core
-- name    : Erdos919.blowup_small_core
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:31:51.756279+00:00
-- url     : https://prove2.me/theorems/4b82ddaa-c4a8-4b4a-bd1a-c695f8574d90
-- title:
--   Erdos919: blowup small core
-- statement:
--   Combinatorial core of the small-type case.
--
--   Source: https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L133-L153
-- source:
--   https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L133-L153

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

theorem Erdos919.blowup_small_core {H : SimpleGraph I} (X : Set (I × I)) (ξ₀ : I) (β : I → I)
    (hβ : ∀ p ∈ X, ξ₀ ≤ p.1 → p.2 < β p.1)
    (c₀ : I → ℕ) (hc₀ : ∀ ξ ξ', ξ < ξ₀ → ξ' < ξ₀ → H.Adj ξ ξ' → c₀ ξ ≠ c₀ ξ')
    (c₁ : I → ℕ) (hc₁ : ∀ ξ ξ', ξ < ξ' → H.Adj ξ ξ' → ξ' < β ξ → c₁ ξ ≠ c₁ ξ') :
    ColorableOn (blowup H) X (Bool × ℕ) := by sorry
