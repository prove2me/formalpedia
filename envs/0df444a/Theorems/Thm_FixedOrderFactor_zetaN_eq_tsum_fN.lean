-- Prove2me | Theorems.Thm_FixedOrderFactor_zetaN_eq_tsum_fN
-- name    : FixedOrderFactor.zetaN_eq_tsum_fN
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:50:30.8044+00:00
-- url     : https://prove2.me/theorems/7ee4e8a5-d695-52c8-b6ad-1bc73cec56fc
-- title:
--   Fixed Order Factor: zeta N eq tsum f N
-- statement:
--   The Fixed Order Factor construction uses the zeta N eq tsum f N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Euler.lean#L44-L46
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Euler.lean#L44-L46

module
public import Definitions.Def_FixedOrderFactor_Defs
public import Definitions.Def_FixedOrderFactor_Euler
set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology
open FixedOrderFactor

theorem FixedOrderFactor.zetaN_eq_tsum_fN (N : Finset Nat.Primes) {s : ℕ} (hs : s ≠ 0) :
    zetaN N s = ∑' n, fN N s hs n := by sorry
