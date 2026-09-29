-- Prove2me | Theorems.Thm_Erdos1210_card_window_small_prime_factor_le
-- name    : Erdos1210.card_window_small_prime_factor_le
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-25T17:08:44.502982+00:00
-- url     : https://prove2.me/theorems/2b9a26f2-1bfb-44e0-939c-3cfbdd0bdad4
-- title:
--   Small-prime-factor elements of a coprime window number at most $\pi(x)$
-- statement:
--   Let $A$ be a finite set of pairwise coprime natural numbers, and let $n,x$ be natural numbers. Then the number of elements $a\in A$ with $a\ge n-x$ that possess a prime factor $p\le x$ is at most $\pi(x)$:
--   $$
--   \#\{a\in A\cap[n-x,\infty):\ \exists p\le x \text{ prime},\ p\mid a\}\le\pi(x).
--   $$
--   This is the first half of the heuristic reduction discussed for Problem 1210: elements of the window $[n-x,n)$ with a small prime factor are controlled by $\pi(x)$, because each prime divides at most one element of a pairwise coprime set. The remaining ($x$-rough) elements are the hard part.
--
--   **Formalization Note** $n-x$ is truncated subtraction ($0$ if $x\ge n$); no upper bound $a<n$ is required.
-- source:
--   erdosproblems.com forum thread for Problem 1210, https://www.erdosproblems.com/forum/thread/1210 , comment by T. Bloom (8 Apr 2026, relaying a suggested argument): 'any prime p ≤ x can divide at most one such a', giving the bound π(x) for elements of A ∩ [n−x, n) with a prime factor < x.

import Mathlib
open Finset

namespace Erdos1210

theorem card_window_small_prime_factor_le (n x : ℕ) (A : Finset ℕ)
    (hcop : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → a.Coprime b) :
    ((A.filter (fun a => n - x ≤ a)).filter
        (fun a => ∃ p ≤ x, p.Prime ∧ p ∣ a)).card ≤ Nat.primeCounting x := by sorry

end Erdos1210
