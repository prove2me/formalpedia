-- Prove2me | Theorems.Thm_FixedOrderFactor_zterm_of
-- name    : FixedOrderFactor.zterm_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:54:31.203985+00:00
-- url     : https://prove2.me/theorems/e0dd30b7-c76b-4b76-ba61-ac6605e1b965
-- title:
--   Fixed Order Factor: zterm of
-- statement:
--   The Fixed Order Factor construction uses the zterm of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Diagonal.lean#L61-L63
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Diagonal.lean#L61-L63

module
public import Definitions.Def_FixedOrderFactor_Values
public import Definitions.Def_FixedOrderFactor_Diagonal
set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Finset
open FixedOrderFactor

theorem FixedOrderFactor.zterm_of {N : Finset Nat.Primes} {s n : ℕ} (h0 : 0 < n) (h : PrimeTo N n) :
    zterm N s n = 1 / (n : ℝ) ^ s := by sorry
