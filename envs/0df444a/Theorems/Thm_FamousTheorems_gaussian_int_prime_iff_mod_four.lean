-- Prove2me | Theorems.Thm_FamousTheorems_gaussian_int_prime_iff_mod_four
-- name    : FamousTheorems.gaussian_int_prime_iff_mod_four
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:38:28.944508+00:00
-- url     : https://prove2.me/theorems/c25965aa-a2c8-4dc5-a002-00ee1f041116
-- title:
--   Rational primes that stay prime in ℤ[i]
-- statement:
--   **Rational primes that stay prime in $\mathbb Z[i]$.** Let $p$ be a prime number. Then $p$ remains prime in the Gaussian integers $\mathbb Z[i]$ if and only if $p\equiv3\pmod 4$.
--
--   The primes $p\equiv1\pmod4$ split as $p=(a+bi)(a-bi)$, and $2=-i(1+i)^2$ ramifies. This is equivalent to Fermat's two-squares theorem. It is the first example of the decomposition of primes in a number field, and it determines all Gaussian primes up to units.
--
--   **Formalization note.** Mathlib's `GaussianInt.prime_iff_mod_four_eq_three_of_nat_prime`. `GaussianInt` is $\mathbb Z[i]$, implemented as `ℤ√-1`, and `Prime` is primality in a commutative monoid.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `GaussianInt.prime_iff_mod_four_eq_three_of_nat_prime`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem gaussian_int_prime_iff_mod_four (p : ℕ) [Fact p.Prime] : Prime (p : GaussianInt) ↔ p % 4 = 3 := by sorry

end FamousTheorems
