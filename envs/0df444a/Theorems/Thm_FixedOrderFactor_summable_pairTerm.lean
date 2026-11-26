-- Prove2me | Theorems.Thm_FixedOrderFactor_summable_pairTerm
-- name    : FixedOrderFactor.summable_pairTerm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:54:16.381919+00:00
-- url     : https://prove2.me/theorems/da076b92-521c-44d9-80b2-56f0dd5e04d8
-- title:
--   Fixed Order Factor: summable pair Term
-- statement:
--   The Fixed Order Factor construction uses the summable pair Term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Diagonal.lean#L46-L48
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Diagonal.lean#L46-L48

module
public import Definitions.Def_FixedOrderFactor_Values
public import Definitions.Def_FixedOrderFactor_Diagonal
set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Finset
open FixedOrderFactor

theorem FixedOrderFactor.summable_pairTerm (N : Finset Nat.Primes) {r : ℕ} (hr : 2 ≤ r) :
    Summable (pairTerm N r) := by sorry
