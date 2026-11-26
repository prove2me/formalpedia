-- Prove2me | Theorems.Thm_FixedOrderFactor_zetaN_eq_mul_prod
-- name    : FixedOrderFactor.zetaN_eq_mul_prod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:50:41.325279+00:00
-- url     : https://prove2.me/theorems/0bf17ba5-ce7a-5181-9c37-2a5bc45b6874
-- title:
--   Fixed Order Factor: zeta N eq mul prod
-- statement:
--   Euler product for `zetaN`, over all primes, with the factors at `N` equal to `1`.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Euler.lean#L98-L112
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Euler.lean#L98-L112

module
public import Definitions.Def_FixedOrderFactor_Defs
public import Definitions.Def_FixedOrderFactor_Euler
set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology
open FixedOrderFactor

theorem FixedOrderFactor.zetaN_eq_mul_prod (N : Finset Nat.Primes) {s : ℕ} (hs : 2 ≤ s) :
    zetaN ∅ s = (∏ q ∈ N, (1 - (1 / (q : ℝ)) ^ s)⁻¹) * zetaN N s := by sorry
