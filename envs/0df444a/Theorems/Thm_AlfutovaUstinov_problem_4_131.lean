-- Prove2me | Theorems.Thm_AlfutovaUstinov_problem_4_131
-- name    : AlfutovaUstinov.problem_4_131
-- status  : Proved
-- author  : @evgeth
-- created : 2026-09-28T23:44:13.558358+00:00
-- url     : https://prove2.me/theorems/60a449d7-3f81-47cb-9a6c-03538327d38a
-- title:
--   Solvability of $x^4+x^3+x^2+x+1\equiv 0 \pmod p$ implies $p\equiv 1 \pmod 5$; infinitely many primes $5n+1$
-- statement:
--   This is Problem 4.131 of N. B. Alfutova and A. V. Ustinov, *Algebra and Number Theory* (MCCME, 2002), Chapter 4, §4 “Theorems of Fermat and Euler”. The problem has two parts.
--
--   1. Let $p>5$ be a prime. If the congruence
--   $$
--   x^{4}+x^{3}+x^{2}+x+1\equiv 0 \pmod p
--   $$
--   has an integer solution $x$, then $p\equiv 1 \pmod 5$.
--
--   2. There are infinitely many primes of the form $5n+1$, $n\in\mathbb N$ (the book asks to deduce this from part 1).
--
--   Part 1 describes the prime divisors of values of the cyclotomic polynomial $\Phi_5(x)=x^4+x^3+x^2+x+1$; part 2 is a special case of Dirichlet's theorem on primes in arithmetic progressions.
--
--   **Formalization Note** Part 1 quantifies over natural numbers $p$ with `Nat.Prime p` and $5<p$, with $x\in\mathbb Z$ and the congruence expressed with `Int.ModEq`; its conclusion uses `Nat.ModEq`. Part 2 states that the set of primes $p$ with $p=5n+1$ for some $n\in\mathbb N$ is infinite.
-- source:
--   N. B. Alfutova, A. V. Ustinov, «Алгебра и теория чисел. Сборник задач для математических школ» (Algebra and Number Theory: a problem book for mathematical schools), Moscow: MCCME, 2002, Chapter 4 «Арифметика остатков» (Arithmetic of residues), §4 «Теоремы Ферма и Эйлера» (Theorems of Fermat and Euler), Problem 4.131. Problem text and answer as catalogued on problems.ru, problem 60757: https://problems.ru/view_problem_details_new.php?id=60757

import Mathlib

namespace AlfutovaUstinov

theorem problem_4_131 :
    (∀ p : ℕ, p.Prime → 5 < p →
        (∃ x : ℤ, x ^ 4 + x ^ 3 + x ^ 2 + x + 1 ≡ 0 [ZMOD p]) → p ≡ 1 [MOD 5]) ∧
      {p : ℕ | p.Prime ∧ ∃ n : ℕ, p = 5 * n + 1}.Infinite := by sorry

end AlfutovaUstinov
