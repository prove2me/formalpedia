-- Prove2me | Theorems.Thm_Erdos287_short_type_ii_nonzero_determinant_fiber_bound
-- name    : Erdos287.short_type_ii_nonzero_determinant_fiber_bound
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T21:23:18.371919+00:00
-- url     : https://prove2.me/theorems/db381685-6ea9-5ad5-a7fc-dacbff88f09b
-- title:
--   Nonzero determinant fiber in the short Type II estimate
-- statement:
--   Fix natural numbers a, b, c with a positive and b distinct from c, and a nonzero integer u. Consider a finite set of triples (k,s,v), with positive natural k and s, k distinct from b and coprime to b, and integer v, satisfying a(b-k)u = ks(b-c)v. If the absolute values of au and a(b-k)u are at most D, and every positive integer at most D has at most C divisors, then the set has at most C squared elements.
-- source:
--   Erdős #287; Fouvry, Autour du théorème de Bombieri–Vinogradov II, (5.8).

import Mathlib

theorem Erdos287.short_type_ii_nonzero_determinant_fiber_bound (a b c D C : ℕ) (u : ℤ) (ha : 0 < a) (hu : u ≠ 0)
    (hbc : b ≠ c) (hD : ((a : ℤ) * u).natAbs ≤ D)
    (hC : ∀ d : ℕ, 0 < d → d ≤ D → d.divisors.card ≤ C)
    (T : Finset (ℕ × ℕ × ℤ))
    (hT : ∀ t ∈ T, 0 < t.1 ∧ 0 < t.2.1 ∧ t.1 ≠ b ∧ t.1.Coprime b ∧
      ((a : ℤ) * ((b : ℤ) - (t.1 : ℤ)) * u).natAbs ≤ D ∧
      (a : ℤ) * ((b : ℤ) - (t.1 : ℤ)) * u =
        (t.1 : ℤ) * (t.2.1 : ℤ) * ((b : ℤ) - (c : ℤ)) * t.2.2) :
    T.card ≤ C * C := by sorry
