-- Prove2me | Theorems.Thm_Erdos287_no_denominator_multiple_of_large_prime_above_third
-- name    : Erdos287.no_denominator_multiple_of_large_prime_above_third
-- status  : Proved
-- author  : @0xbf
-- created : 2026-11-11T19:33:40.354519+00:00
-- url     : https://prove2.me/theorems/00bbdb86-1f33-44bf-87f7-cb87f8c5be26
-- title:
--   No denominator is divisible by a prime above one third of the range
-- statement:
--   Let $k\ge 2$ and let $n_0,\ldots,n_{k-1}$ be pairwise distinct integers greater than $1$, all bounded by $N$, such that
--
--   $$\sum_{i<k}\frac{1}{n_i}=1.$$
--
--   For any prime $p>3$ with $N<3p$, no denominator is divisible by $p$:
--
--   $$\forall i<k,\quad p\nmid n_i.$$
--
--   Equivalently, every prime factor greater than $3$ that occurs in a denominator is at most $N/3$. This is a p-adic exclusion constraint for Egyptian-fraction representations, and can be used alongside restrictions on the spacing of denominators.
-- source:
--   Auxiliary result derived from the proved p-adic multiplicity theorem in the Erdős Problem 287 mission; see https://www.erdosproblems.com/287.

import Mathlib.NumberTheory.Padics.PadicNorm
import Mathlib.Tactic

namespace Erdos287
theorem no_denominator_multiple_of_large_prime_above_third
    (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (hdist : ∀ i j, i < k → j < k → i ≠ j → f i ≠ f j)
    (N : ℕ) (hbound : ∀ i, i < k → f i ≤ N)
    (p : ℕ) (hp : Nat.Prime p) (hp3 : 3 < p) (hN : N < 3 * p)
    (i : ℕ) (hi : i < k) : ¬ p ∣ f i := by sorry
end Erdos287
