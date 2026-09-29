-- Prove2me | Theorems.Thm_AlfutovaUstinov_problem_4_126
-- name    : AlfutovaUstinov.problem_4_126
-- status  : Proved
-- author  : @evgeth
-- created : 2026-09-28T23:44:01.943902+00:00
-- url     : https://prove2.me/theorems/201824f6-ca7a-429f-9ab9-32ce65952923
-- title:
--   Odd prime divisors of $x^2+1$ have the form $4k+1$
-- statement:
--   This is Problem 4.126 of N. B. Alfutova and A. V. Ustinov, *Algebra and Number Theory* (MCCME, 2002), Chapter 4, §4 “Theorems of Fermat and Euler”.
--
--   **Theorem.** Let $x$ be an integer and let $p$ be an odd prime such that
--
--   $$
--   p \mid x^{2}+1 .
--   $$
--
--   Then $p$ has the form $p=4k+1$ for some natural number $k$.
--
--   This classical fact (the only prime divisors of $x^2+1$ are $2$ and primes $\equiv 1 \pmod 4$) is used in the book's next problem to prove that there are infinitely many primes of the form $4k+1$.
--
--   **Formalization Note** The prime $p$ is a natural number with `Nat.Prime p` and `Odd p`; the integer $x$ is arbitrary and divisibility is taken in $\mathbb Z$.
-- source:
--   N. B. Alfutova, A. V. Ustinov, «Алгебра и теория чисел. Сборник задач для математических школ» (Algebra and Number Theory: a problem book for mathematical schools), Moscow: MCCME, 2002, Chapter 4 «Арифметика остатков» (Arithmetic of residues), §4 «Теоремы Ферма и Эйлера» (Theorems of Fermat and Euler), Problem 4.126. Problem text and answer as catalogued on problems.ru, problem 60752: https://problems.ru/view_problem_details_new.php?id=60752

import Mathlib

namespace AlfutovaUstinov

theorem problem_4_126 (p : ℕ) (hp : p.Prime) (hodd : Odd p) (x : ℤ) (hx : (p : ℤ) ∣ x ^ 2 + 1) :
    ∃ k : ℕ, p = 4 * k + 1 := by sorry

end AlfutovaUstinov
