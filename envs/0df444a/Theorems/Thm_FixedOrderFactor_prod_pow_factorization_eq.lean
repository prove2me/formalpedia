-- Prove2me | Theorems.Thm_FixedOrderFactor_prod_pow_factorization_eq
-- name    : FixedOrderFactor.prod_pow_factorization_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:55:13.948745+00:00
-- url     : https://prove2.me/theorems/3b8bdad9-a253-46d7-ab25-f8dc36cd941a
-- title:
--   Fixed Order Factor: prod pow factorization eq
-- statement:
--   `∏_{q ∈ S} q^{v_q(m)} = m` when every prime factor of `m` lies in `S`.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/ModelPairs.lean#L49-L72
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/ModelPairs.lean#L49-L72

module
public import Definitions.Def_FixedOrderFactor_Defs
public import Definitions.Def_FixedOrderFactor_Pairs
public import Definitions.Def_FixedOrderFactor_ModelPairs
set_option autoImplicit true
@[expose] public section
public section
open Finset Complex
open FixedOrderFactor

theorem FixedOrderFactor.prod_pow_factorization_eq {S : Finset Nat.Primes} {m : ℕ} (hm : 0 < m)
    (hS : ∀ q : Nat.Primes, (q : ℕ) ∣ m → q ∈ S) :
    ∏ q ∈ S, ((q : ℕ) : ℚ) ^ (m.factorization q) = m := by sorry
