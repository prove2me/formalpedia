-- Prove2me | Theorems.Thm_Erdos287_dispersion_quotient_congruence
-- name    : Erdos287.dispersion_quotient_congruence
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T04:26:46.637308+00:00
-- url     : https://prove2.me/theorems/c708dd14-e08c-4e8c-8d4d-8a3e2543c56f
-- title:
--   Dispersion congruence with a shared modulus
-- statement:
--   Let n₁−n₂=s k with s nonzero. If x n₁−a is divisible by r₁s and x n₂−a is divisible by r₂s, write x n₁=a+r₁s l. Then r₂n₁ divides r₁n₂l−ak.
-- source:
--   Erdős Problem #287, mixed-residue sieve. The shared-modulus calculation is relevant to the reciprocity step in Zongkun Zheng, Primes in simultaneous arithmetic progressions, arXiv:2512.22798, Lemma 2.5.

import Mathlib

theorem Erdos287.dispersion_quotient_congruence (a x n₁ n₂ r₁ r₂ s k : ℤ)
    (hs : s ≠ 0) (hdiff : n₁ - n₂ = s * k)
    (h₁ : r₁ * s ∣ x * n₁ - a) (h₂ : r₂ * s ∣ x * n₂ - a) :
    ∃ l : ℤ, x * n₁ = a + r₁ * s * l ∧ r₂ * n₁ ∣ r₁ * n₂ * l - a * k := by sorry
