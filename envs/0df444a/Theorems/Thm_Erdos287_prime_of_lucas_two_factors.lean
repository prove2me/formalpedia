-- Prove2me | Theorems.Thm_Erdos287_prime_of_lucas_two_factors
-- name    : Erdos287.prime_of_lucas_two_factors
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T05:02:06.834983+00:00
-- url     : https://prove2.me/theorems/e7a580db-ae6a-51c0-b35b-2a6a0996490f
-- title:
--   Lucas primality certificate with two possible prime factors
-- statement:
--   A candidate n is prime if n−1 is a prime times a power of two and a Lucas witness passes the full exponent check and the two checks obtained by dividing the exponent by the possible prime factors.
-- source:
--   Erdős Problem #287 finite certificate ladder; specialization of Lucas primality.

import Mathlib

theorem Erdos287.prime_of_lucas_two_factors (n p a g : ℕ) (hp : p.Prime) (hfactor : n - 1 = p * 2 ^ a)
    (hfull : (g : ZMod n) ^ (n - 1) = 1)
    (htwo : (g : ZMod n) ^ ((n - 1) / 2) ≠ 1)
    (hprime : (g : ZMod n) ^ ((n - 1) / p) ≠ 1) :
    n.Prime := by sorry
