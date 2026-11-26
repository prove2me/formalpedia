-- Prove2me | Theorems.Thm_Erdos287_large_prime_removes_exceptional_conductor
-- name    : Erdos287.large_prime_removes_exceptional_conductor
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T20:14:26.282473+00:00
-- url     : https://prove2.me/theorems/a4efe044-107e-57d1-a472-11ebcc68f785
-- title:
--   Removing an exceptional conductor by one large prime
-- statement:
--   Suppose $d$ is squarefree, $d\mid r$, $r\mid bd$, $b>0$, and $b4^w<r$. There is a prime $p>w$ dividing $r$. Any product of factors avoiding $p$ also avoids $r$ as a divisor. For real numbers $0\le\eta\le\nu\le K$ and $2K<p$, the local density ratio $(p-\eta)/(p-\nu)$ is between one and $1+2K/p$.
-- source:
--   Erdős #287 sieve effectivity. Ford, Green, Konyagin, Maynard and Tao, Long gaps between primes, Lemma 7.1.

import Mathlib

theorem Erdos287.large_prime_removes_exceptional_conductor (r d b w : ℕ) (hs : Squarefree d)
    (hr : r ∣ b * d) (hd : d ∣ r) (hb : 0 < b) (hlarge : b * 4 ^ w < r) :
    ∃ p : ℕ, p.Prime ∧ w < p ∧ p ∣ r ∧
      (∀ (ι : Type) (T : Finset ι) (m : ι → ℕ),
        (∀ i ∈ T, ¬ p ∣ m i) → ¬ r ∣ ∏ i ∈ T, m i) ∧
      (∀ K ν η : ℝ, 0 ≤ η → η ≤ ν → ν ≤ K → 2 * K < p →
        0 ≤ ((p : ℝ) - η) / ((p : ℝ) - ν) - 1 ∧
        ((p : ℝ) - η) / ((p : ℝ) - ν) - 1 ≤ 2 * K / p) := by sorry
