-- Prove2me | Theorems.Thm_Erdos1063_prod_prime_pow_dvd
-- name    : Erdos1063.prod_prime_pow_dvd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:30:51.814471+00:00
-- url     : https://prove2.me/theorems/1c944c78-35a6-5ae2-a904-71f9725ac49b
-- title:
--   Erdos1063: prod prime pow dvd
-- statement:
--   A product of powers of distinct primes divides `m` if each factor does.
--
--   Source: https://github.com/Paulee314/erdos1063-lean/blob/ba104cbcf0bb7c555a8b2f0d58018989a08c638e/Erdos1063/Lower.lean#L213-L227
-- source:
--   https://github.com/Paulee314/erdos1063-lean/blob/ba104cbcf0bb7c555a8b2f0d58018989a08c638e/Erdos1063/Lower.lean#L213-L227

module
public import Mathlib
public import Definitions.Def_Erdos1063_Lower
set_option autoImplicit false
@[expose] public section
public section
open Finset
open scoped Nat
open Erdos1063

theorem Erdos1063.prod_prime_pow_dvd {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) (f : ℕ → ℕ) {m : ℕ}
    (h : ∀ p ∈ s, p ^ f p ∣ m) : ∏ p ∈ s, p ^ f p ∣ m := by sorry
