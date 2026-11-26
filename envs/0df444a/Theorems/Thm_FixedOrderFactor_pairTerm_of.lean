-- Prove2me | Theorems.Thm_FixedOrderFactor_pairTerm_of
-- name    : FixedOrderFactor.pairTerm_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:53:57.400616+00:00
-- url     : https://prove2.me/theorems/bd98dae0-08c5-5a7c-a7a6-ae94220e277a
-- title:
--   Fixed Order Factor: pair Term of
-- statement:
--   The Fixed Order Factor construction uses the pair Term of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Diagonal.lean#L65-L68
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Diagonal.lean#L65-L68

module
public import Definitions.Def_FixedOrderFactor_Values
public import Definitions.Def_FixedOrderFactor_Diagonal
set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Finset
open FixedOrderFactor

theorem FixedOrderFactor.pairTerm_of {N : Finset Nat.Primes} {r : ℕ} {ab : ℕ × ℕ}
    (h : 0 < ab.1 ∧ 0 < ab.2 ∧ Nat.Coprime ab.1 ab.2 ∧ PrimeTo N ab.1 ∧ PrimeTo N ab.2) :
    pairTerm N r ab = 1 / ((ab.1 * ab.2 : ℕ) : ℝ) ^ r := by sorry
