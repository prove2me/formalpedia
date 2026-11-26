-- Prove2me | Theorems.Thm_FixedOrderFactor_primeTo_of_dvd
-- name    : FixedOrderFactor.primeTo_of_dvd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:53:25.112806+00:00
-- url     : https://prove2.me/theorems/ff553237-f469-5d19-9e1b-c551ca846a48
-- title:
--   Fixed Order Factor: prime To of dvd
-- statement:
--   The Fixed Order Factor construction uses the prime To of dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Diagonal.lean#L50-L51
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Diagonal.lean#L50-L51

module
public import Definitions.Def_FixedOrderFactor_Values
public import Definitions.Def_FixedOrderFactor_Diagonal
set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Finset
open FixedOrderFactor

theorem FixedOrderFactor.primeTo_of_dvd {N : Finset Nat.Primes} {m n : ℕ} (h : PrimeTo N n) (hmn : m ∣ n) :
    PrimeTo N m := by sorry
