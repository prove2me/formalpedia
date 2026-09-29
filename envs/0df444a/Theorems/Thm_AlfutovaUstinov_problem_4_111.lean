-- Prove2me | Theorems.Thm_AlfutovaUstinov_problem_4_111
-- name    : AlfutovaUstinov.problem_4_111
-- status  : Proved
-- author  : @evgeth
-- created : 2026-09-28T23:43:21.388426+00:00
-- url     : https://prove2.me/theorems/1e28b432-7475-45db-b0ac-6173fae7ff91
-- title:
--   Every prime $p\ne 2,5$ divides some repunit $11\ldots1$
-- statement:
--   This is Problem 4.111 of N. B. Alfutova and A. V. Ustinov, *Algebra and Number Theory* (MCCME, 2002), Chapter 4, §4 “Theorems of Fermat and Euler”.
--
--   A *repunit* is a natural number whose decimal representation consists of ones only. For $k\ge 1$ the repunit with $k$ digits is
--
--   $$
--   R_k=\underbrace{11\ldots1}_{k\ \text{digits}}=\sum_{i=0}^{k-1}10^{i}.
--   $$
--
--   **Theorem.** Let $p$ be a prime number with $p\ne 2$ and $p\ne 5$. Then some repunit is a multiple of $p$: there exists $k\ge 1$ with
--
--   $$
--   p \mid \sum_{i=0}^{k-1}10^{i}.
--   $$
--
--   The primes $2$ and $5$ are exactly the prime divisors of the base $10$, and no repunit is divisible by them. The result is closely related to the fact that $1/p$ has a purely periodic decimal expansion for such $p$.
--
--   **Formalization Note** The repunit $R_k$ is written as the finite sum $\sum_{i\in\{0,\dots,k-1\}}10^i$ (`Finset.range k`), and the number of digits $k$ is required to be positive.
-- source:
--   N. B. Alfutova, A. V. Ustinov, «Алгебра и теория чисел. Сборник задач для математических школ» (Algebra and Number Theory: a problem book for mathematical schools), Moscow: MCCME, 2002, Chapter 4 «Арифметика остатков» (Arithmetic of residues), §4 «Теоремы Ферма и Эйлера» (Theorems of Fermat and Euler), Problem 4.111. Problem text and answer as catalogued on problems.ru, problem 60737: https://problems.ru/view_problem_details_new.php?id=60737

import Mathlib

namespace AlfutovaUstinov

theorem problem_4_111 (p : ℕ) (hp : p.Prime) (h2 : p ≠ 2) (h5 : p ≠ 5) :
    ∃ k : ℕ, 0 < k ∧ p ∣ ∑ i ∈ Finset.range k, 10 ^ i := by sorry

end AlfutovaUstinov
