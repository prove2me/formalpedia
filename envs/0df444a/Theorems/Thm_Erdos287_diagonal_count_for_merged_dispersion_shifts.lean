-- Prove2me | Theorems.Thm_Erdos287_diagonal_count_for_merged_dispersion_shifts
-- name    : Erdos287.diagonal_count_for_merged_dispersion_shifts
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T20:26:18.085737+00:00
-- url     : https://prove2.me/theorems/e4f62b3d-0cbc-5547-a177-56b52412707e
-- title:
--   Diagonal count with two dispersion shifts
-- statement:
--   Let $n,n^\prime,B$ be positive integers, and let $C$ bound the number of divisors of each positive integer at most $D$. Consider distinct tuples $(u,u^\prime,k,k^\prime,a)$ with $1\le u,u^\prime\le D$, $un^\prime=u^\prime n$, $k\mid u$, $k^\prime\mid u^\prime$, $a\le 2N$, $B\le\max(k,k^\prime)$, $a\equiv n\pmod{k}$, and $a\equiv n^\prime\pmod{k^\prime}$. Their number is at most $\lfloor D/(n^\prime/\gcd(n,n^\prime))\rfloor C^2(1+\lfloor 2N/B\rfloor)$.
-- source:
--   Erdős #287, Type II dispersion with a fixed auxiliary modulus.

import Mathlib

theorem Erdos287.diagonal_count_for_merged_dispersion_shifts (n n' N L D C : ℕ) (hn : 0 < n) (hn' : 0 < n') (hL : 0 < L)
    (hC : ∀ u, 0 < u → u ≤ D → u.divisors.card ≤ C)
    (T : Finset ((ℕ × ℕ) × (ℕ × ℕ × ℕ)))
    (hT : ∀ t ∈ T, 0 < t.1.1 ∧ t.1.1 ≤ D ∧ 0 < t.1.2 ∧ t.1.2 ≤ D ∧
      t.1.1 * n' = t.1.2 * n ∧ t.2.1 ∣ t.1.1 ∧ t.2.2.1 ∣ t.1.2 ∧
      t.2.2.2 ≤ 2 * N ∧ L ≤ max t.2.1 t.2.2.1 ∧
      t.2.2.2 ≡ n [MOD t.2.1] ∧ t.2.2.2 ≡ n' [MOD t.2.2.1]) :
    T.card ≤ (D / (n' / n.gcd n')) * (C * C * (2 * N / L + 1)) := by sorry
