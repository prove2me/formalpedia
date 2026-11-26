-- Prove2me | Theorems.Thm_FixedOrderFactor_mem_powers_iff
-- name    : FixedOrderFactor.mem_powers_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:47:09.424489+00:00
-- url     : https://prove2.me/theorems/2ab3b978-0b3e-40f0-9742-b2a1e9cbc0b3
-- title:
--   Fixed Order Factor: mem powers iff
-- statement:
--   The Fixed Order Factor construction uses the mem powers iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Characters.lean#L73-L80
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Characters.lean#L73-L80

module
public import Mathlib
public import Definitions.Def_FixedOrderFactor_Characters
set_option autoImplicit true
@[expose] public section
public section
open Finset
open FixedOrderFactor
variable (p : ℕ) [Fact p.Prime]

theorem FixedOrderFactor.mem_powers_iff (r : ℕ) (u : (ZMod p)ˣ) :
    u ∈ powers p r ↔ ∃ c : ZMod p, c ≠ 0 ∧ (u : ZMod p) = c ^ r := by sorry
