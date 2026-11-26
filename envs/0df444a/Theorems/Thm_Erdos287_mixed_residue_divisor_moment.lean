-- Prove2me | Theorems.Thm_Erdos287_mixed_residue_divisor_moment
-- name    : Erdos287.mixed_residue_divisor_moment
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T04:05:13.591803+00:00
-- url     : https://prove2.me/theorems/6bee17ae-9f7e-4a12-8654-6eb4f2d64e34
-- title:
--   Divisor moment bound for a finite menu of local residues
-- statement:
--   Suppose each squarefree q in a finite set divides y-A, and at each prime p dividing q the residue of C*A agrees with some fixed menu value c_i modulo p. If C*y differs from every c_i, the sum over q of tau(q)^B is at most tau(|product_i (C*y-c_i)|)^(B+1).
-- source:
--   Erdős Problem #287, analytic sieve reduction. The divisor count is relevant to the dispersion step in Zongkun Zheng, Primes in simultaneous arithmetic progressions, arXiv:2512.22798, Section 3.3.

import Mathlib

theorem Erdos287.mixed_residue_divisor_moment (k : ℕ) (c : Fin k → ℤ) (C A y : ℤ)
    (hy : ∀ i, C * y ≠ c i) (Q : Finset ℕ)
    (hsq : ∀ q ∈ Q, Squarefree q)
    (hmenu : ∀ q ∈ Q, ∀ p : ℕ, p.Prime → p ∣ q →
      ∃ i, (p : ℤ) ∣ C * A - c i)
    (hres : ∀ q ∈ Q, (q : ℤ) ∣ y - A)
    (B : ℕ) :
    (∑ q ∈ Q, q.divisors.card ^ B) ≤
      (∏ i : Fin k, (C * y - c i)).natAbs.divisors.card ^ (B + 1) := by sorry
