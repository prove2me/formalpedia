-- Prove2me | Theorems.Thm_FixedOrderFactor_hasProd_zetaN
-- name    : FixedOrderFactor.hasProd_zetaN
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:47:41.354693+00:00
-- url     : https://prove2.me/theorems/b0ea9c46-c9b8-5fb5-9a97-138ffffb7065
-- title:
--   Fixed Order Factor: has Prod zeta N
-- statement:
--   Euler product for `zetaN`, over the primes outside `N`.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Euler.lean#L49-L70
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Euler.lean#L49-L70

module
public import Definitions.Def_FixedOrderFactor_Defs
public import Definitions.Def_FixedOrderFactor_Euler
set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology
open FixedOrderFactor

theorem FixedOrderFactor.hasProd_zetaN (N : Finset Nat.Primes) {s : ℕ} (hs : 2 ≤ s) :
    HasProd (fun q : {q : Nat.Primes // q ∉ N} => (1 - (1 / (q : ℝ)) ^ s)⁻¹) (zetaN N s) := by sorry
