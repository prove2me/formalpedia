-- Prove2me | Theorems.Thm_FixedOrderFactor_zterm_ne_zero
-- name    : FixedOrderFactor.zterm_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:53:35.60205+00:00
-- url     : https://prove2.me/theorems/f36fa6bd-3d8d-58f6-9b62-7c1ed5955572
-- title:
--   Fixed Order Factor: zterm ne zero
-- statement:
--   The Fixed Order Factor construction uses the zterm ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Diagonal.lean#L53-L55
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Diagonal.lean#L53-L55

module
public import Definitions.Def_FixedOrderFactor_Values
public import Definitions.Def_FixedOrderFactor_Diagonal
set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Finset
open FixedOrderFactor

theorem FixedOrderFactor.zterm_ne_zero {N : Finset Nat.Primes} {s n : ℕ} (h : zterm N s n ≠ 0) :
    0 < n ∧ PrimeTo N n := by sorry
