-- Prove2me | Theorems.Thm_AlfutovaUstinov_problem_4_122
-- name    : AlfutovaUstinov.problem_4_122
-- status  : Proved
-- author  : @evgeth
-- created : 2026-09-28T23:43:50.195524+00:00
-- url     : https://prove2.me/theorems/70f8c6be-91dc-4cbf-a2e4-48c33f7b489e
-- title:
--   Prime divisors of $2^p-1$ have the form $2kp+1$
-- statement:
--   This is Problem 4.122 of N. B. Alfutova and A. V. Ustinov, *Algebra and Number Theory* (MCCME, 2002), Chapter 4, §4 “Theorems of Fermat and Euler”.
--
--   **Theorem.** Let $p>2$ be a prime number. Then every prime divisor $q$ of the Mersenne number $2^{p}-1$ has the form
--
--   $$
--   q = 2kp+1
--   $$
--
--   for some natural number $k$.
--
--   This classical fact about Mersenne numbers (going back to Fermat and Euler) drastically restricts the possible prime factors of $2^p-1$ and is used when searching for Mersenne primes.
--
--   **Formalization Note** Here $p$ and $q$ are natural numbers with `Nat.Prime`; the subtraction $2^p-1$ is natural-number subtraction, which is exact since $2^p\ge 1$.
-- source:
--   N. B. Alfutova, A. V. Ustinov, «Алгебра и теория чисел. Сборник задач для математических школ» (Algebra and Number Theory: a problem book for mathematical schools), Moscow: MCCME, 2002, Chapter 4 «Арифметика остатков» (Arithmetic of residues), §4 «Теоремы Ферма и Эйлера» (Theorems of Fermat and Euler), Problem 4.122. Problem text and answer as catalogued on problems.ru, problem 60748: https://problems.ru/view_problem_details_new.php?id=60748

import Mathlib

namespace AlfutovaUstinov

theorem problem_4_122 (p : ℕ) (hp : p.Prime) (hp2 : 2 < p) (q : ℕ) (hq : q.Prime)
    (hqd : q ∣ 2 ^ p - 1) : ∃ k : ℕ, q = 2 * k * p + 1 := by sorry

end AlfutovaUstinov
