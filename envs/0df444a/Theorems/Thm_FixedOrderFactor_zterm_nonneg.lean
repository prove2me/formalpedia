-- Prove2me | Theorems.Thm_FixedOrderFactor_zterm_nonneg
-- name    : FixedOrderFactor.zterm_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:50:05.108968+00:00
-- url     : https://prove2.me/theorems/e70e0e44-1665-56b8-a336-2c693555a723
-- title:
--   Fixed Order Factor: zterm nonneg
-- statement:
--   The Fixed Order Factor construction uses the zterm nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Diagonal.lean#L19-L20
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Diagonal.lean#L19-L20

module
public import Definitions.Def_FixedOrderFactor_Values
public import Definitions.Def_FixedOrderFactor_Diagonal
set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Finset
open FixedOrderFactor

theorem FixedOrderFactor.zterm_nonneg (N : Finset Nat.Primes) (s n : ℕ) : 0 ≤ zterm N s n := by sorry
