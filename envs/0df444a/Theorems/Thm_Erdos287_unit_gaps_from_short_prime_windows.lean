-- Prove2me | Theorems.Thm_Erdos287_unit_gaps_from_short_prime_windows
-- name    : Erdos287.unit_gaps_from_short_prime_windows
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T03:04:45.718166+00:00
-- url     : https://prove2.me/theorems/e2cc3dda-b883-4e1d-9c68-f14a6f6d56ab
-- title:
--   Short windows containing a prime and twice a prime force unit gaps
-- statement:
--   Let $1<n_0<\cdots<n_{k-1}=M$ have reciprocal sum one, with $M\ge12$ and every consecutive gap at most two. Fix a nonnegative integer $w$ and a finite set $S$ of integer starting positions. Suppose for every $s\in S$ the interval $[s,s+w]$ lies in $[3M/4,M)$ and contains both a prime $p$ and twice a prime $2q$. If $t$ is the number of consecutive gaps equal to one, then $|S|\le(w+1)t$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287. The asymptotic application uses Chaohua Jia, Almost all short intervals containing prime numbers, Acta Arith. 76 (1996), 21–84, https://doi.org/10.4064/aa-76-1-21-84.

import Mathlib

theorem Erdos287.unit_gaps_from_short_prime_windows (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (hgap : ∀ i, i + 1 < k → f (i + 1) - f i ≤ 2)
    (hM : 12 ≤ f (k - 1)) (S : Finset ℕ) (w : ℕ)
    (hwindows : ∀ s ∈ S, 3 * f (k - 1) ≤ 4 * s ∧ s + w < f (k - 1) ∧
      ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ s ≤ p ∧ p ≤ s + w ∧ s ≤ 2 * q ∧ 2 * q ≤ s + w) :
    S.card ≤ (w + 1) * ((Finset.range (k - 1)).filter (fun i => f (i + 1) - f i = 1)).card := by sorry
