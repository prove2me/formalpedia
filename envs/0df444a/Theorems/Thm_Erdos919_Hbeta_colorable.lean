-- Prove2me | Theorems.Thm_Erdos919_Hbeta_colorable
-- name    : Erdos919.Hbeta_colorable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:31:24.598823+00:00
-- url     : https://prove2.me/theorems/bc6ea3a3-af0a-516d-ad68-2f0cb19036a9
-- title:
--   Erdos919: Hbeta colorable
-- statement:
--   Gluing countable colourings of the bounded blocks between consecutive closure points.
--
--   Source: https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L156-L178
-- source:
--   https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L156-L178

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

theorem Erdos919.Hbeta_colorable [WellFoundedLT I] {H : SimpleGraph I}
    (hinit : ∀ a : I, ∃ c : I → ℕ, ∀ ξ ξ', ξ < a → ξ' < a → H.Adj ξ ξ' → c ξ ≠ c ξ')
    (β : I → I) (hclub : ∀ a : I, ∃ δ, a < δ ∧ ∀ ζ < δ, β ζ ≤ δ) :
    ∃ c₁ : I → ℕ, ∀ ξ ξ', ξ < ξ' → H.Adj ξ ξ' → ξ' < β ξ → c₁ ξ ≠ c₁ ξ' := by sorry
