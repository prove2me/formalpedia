-- Prove2me | Theorems.Thm_FixedOrderFactor_pairTerm_ne_zero
-- name    : FixedOrderFactor.pairTerm_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:53:39.217949+00:00
-- url     : https://prove2.me/theorems/16671b8e-52d2-5fae-9314-1f3cee51e828
-- title:
--   Fixed Order Factor: pair Term ne zero
-- statement:
--   The Fixed Order Factor construction uses the pair Term ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Diagonal.lean#L57-L59
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Diagonal.lean#L57-L59

module
public import Definitions.Def_FixedOrderFactor_Values
public import Definitions.Def_FixedOrderFactor_Diagonal
set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Finset
open FixedOrderFactor

theorem FixedOrderFactor.pairTerm_ne_zero {N : Finset Nat.Primes} {r : ℕ} {ab : ℕ × ℕ} (h : pairTerm N r ab ≠ 0) :
    0 < ab.1 ∧ 0 < ab.2 ∧ Nat.Coprime ab.1 ab.2 ∧ PrimeTo N ab.1 ∧ PrimeTo N ab.2 := by sorry
