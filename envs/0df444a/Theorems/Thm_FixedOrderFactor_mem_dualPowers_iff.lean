-- Prove2me | Theorems.Thm_FixedOrderFactor_mem_dualPowers_iff
-- name    : FixedOrderFactor.mem_dualPowers_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:46:54.858304+00:00
-- url     : https://prove2.me/theorems/3f2514ba-6e46-5d03-8d39-0df0a6bf915d
-- title:
--   Fixed Order Factor: mem dual Powers iff
-- statement:
--   The Fixed Order Factor construction uses the mem dual Powers iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Characters.lean#L22-L32
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Characters.lean#L22-L32

module
public import Mathlib
public import Definitions.Def_FixedOrderFactor_Characters
set_option autoImplicit true
@[expose] public section
public section
open Finset
open FixedOrderFactor
variable (p : ℕ) [Fact p.Prime]

theorem FixedOrderFactor.mem_dualPowers_iff (r : ℕ) (χ : MulChar (ZMod p) ℂ) :
    χ ∈ dualPowers p r ↔ χ ^ r = 1 := by sorry
