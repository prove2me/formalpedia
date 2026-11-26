-- Prove2me | Theorems.Thm_FixedOrderFactor_summable_zetaN_terms
-- name    : FixedOrderFactor.summable_zetaN_terms
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:47:45.127707+00:00
-- url     : https://prove2.me/theorems/b73ab179-e269-5f46-b0cd-356799c23fae
-- title:
--   Fixed Order Factor: summable zeta N terms
-- statement:
--   The Fixed Order Factor construction uses the summable zeta N terms property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Euler.lean#L73-L75
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Euler.lean#L73-L75

module
public import Definitions.Def_FixedOrderFactor_Defs
public import Definitions.Def_FixedOrderFactor_Euler
set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology
open FixedOrderFactor

theorem FixedOrderFactor.summable_zetaN_terms (N : Finset Nat.Primes) {s : ℕ} (hs : 2 ≤ s) :
    Summable (fun n : ℕ => if 0 < n ∧ PrimeTo N n then 1 / (n : ℝ) ^ s else 0) := by sorry
