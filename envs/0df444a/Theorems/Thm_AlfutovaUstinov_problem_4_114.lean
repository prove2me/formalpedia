-- Prove2me | Theorems.Thm_AlfutovaUstinov_problem_4_114
-- name    : AlfutovaUstinov.problem_4_114
-- status  : Proved
-- author  : @evgeth
-- created : 2026-09-28T23:43:29.268436+00:00
-- url     : https://prove2.me/theorems/b3560103-c1b7-405d-917d-69d17c1eb48d
-- title:
--   The order of $a$ modulo a prime $p$ divides $p-1$
-- statement:
--   This is Problem 4.114 of N. B. Alfutova and A. V. Ustinov, *Algebra and Number Theory* (MCCME, 2002), Chapter 4, §4 “Theorems of Fermat and Euler”.
--
--   Let $p$ be a prime and let $a$ be an integer not divisible by $p$. Let $k$ be the least positive integer such that
--
--   $$
--   a^{k}\equiv 1 \pmod p
--   $$
--
--   (the *multiplicative order* of $a$ modulo $p$).
--
--   **Theorem.** Under these assumptions,
--
--   $$
--   k \mid p-1 .
--   $$
--
--   This is the basic link between Fermat's little theorem and the orders of residues modulo a prime; it is the starting point of the theory of primitive roots.
--
--   **Formalization Note** The minimality of $k$ is expressed by `IsLeast {j : ℕ | 0 < j ∧ a ^ j ≡ 1 [ZMOD p]} k`: the number $k$ is a positive exponent with $a^k\equiv 1 \pmod p$, and every positive exponent $j$ with $a^j\equiv1\pmod p$ satisfies $k\le j$.
-- source:
--   N. B. Alfutova, A. V. Ustinov, «Алгебра и теория чисел. Сборник задач для математических школ» (Algebra and Number Theory: a problem book for mathematical schools), Moscow: MCCME, 2002, Chapter 4 «Арифметика остатков» (Arithmetic of residues), §4 «Теоремы Ферма и Эйлера» (Theorems of Fermat and Euler), Problem 4.114. Problem text and answer as catalogued on problems.ru, problem 60740: https://problems.ru/view_problem_details_new.php?id=60740

import Mathlib

namespace AlfutovaUstinov

theorem problem_4_114 (p : ℕ) (hp : p.Prime) (a : ℤ) (ha : ¬ (p : ℤ) ∣ a) (k : ℕ)
    (hk : IsLeast {j : ℕ | 0 < j ∧ a ^ j ≡ 1 [ZMOD p]} k) : k ∣ p - 1 := by sorry

end AlfutovaUstinov
