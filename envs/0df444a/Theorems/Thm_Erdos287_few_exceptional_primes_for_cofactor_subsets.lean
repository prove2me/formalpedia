-- Prove2me | Theorems.Thm_Erdos287_few_exceptional_primes_for_cofactor_subsets
-- name    : Erdos287.few_exceptional_primes_for_cofactor_subsets
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T07:00:53.758894+00:00
-- url     : https://prove2.me/theorems/d0584465-4045-5b3b-b515-d82a4f8391b0
-- title:
--   Few large primes can divide cleared numerators of admissible cofactor sets
-- statement:
--   Let $U$ be a finite set of positive divisors of $L>0$, and let $F$ be a finite family of nonempty subsets of $U$. Suppose $Y\ge2$ and $|U|L<Y^{K+1}$. If each prime in a finite set $P$ is at least $Y$ and divides $\sum_{b\in T}L/b$ for some $T\in F$, then $|P|\le K|F|$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287. Finite exceptional-prime counting for highest prime layers.

import Mathlib

theorem Erdos287.few_exceptional_primes_for_cofactor_subsets (U P : Finset ℕ) (F : Finset (Finset ℕ)) (L Y K : ℕ)
    (hL : 0 < L) (hY : 2 ≤ Y) (hU : ∀ n ∈ U, 0 < n ∧ n ∣ L)
    (hF : ∀ T ∈ F, T ⊆ U ∧ T.Nonempty)
    (hP : ∀ p ∈ P, p.Prime ∧ Y ≤ p)
    (hbound : U.card * L < Y ^ (K + 1))
    (hexception : ∀ p ∈ P, ∃ T ∈ F, p ∣ ∑ n ∈ T, L / n) :
    P.card ≤ F.card * K := by sorry
