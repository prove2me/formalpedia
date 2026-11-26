-- Prove2me | Theorems.Thm_FixedOrderFactor_zetaN_eq
-- name    : FixedOrderFactor.zetaN_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:48:57.407567+00:00
-- url     : https://prove2.me/theorems/1d0060a1-4088-5dbb-a7da-e273abe1c1aa
-- title:
--   Fixed Order Factor: zeta N eq
-- statement:
--   The Fixed Order Factor construction uses the zeta N eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Euler.lean#L114-L121
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Euler.lean#L114-L121

module
public import Definitions.Def_FixedOrderFactor_Defs
public import Definitions.Def_FixedOrderFactor_Euler
set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology
open FixedOrderFactor

theorem FixedOrderFactor.zetaN_eq (N : Finset Nat.Primes) {s : ℕ} (hs : 2 ≤ s) :
    zetaN N s = zetaN ∅ s * ∏ q ∈ N, (1 - (1 / (q : ℝ)) ^ s) := by sorry
