-- Prove2me | Theorems.Thm_AlfutovaUstinov_problem_4_118
-- name    : AlfutovaUstinov.problem_4_118
-- status  : Proved
-- author  : @evgeth
-- created : 2026-09-28T23:43:38.019522+00:00
-- url     : https://prove2.me/theorems/0e5e207d-c2a9-4088-a5c5-fe3f3e5fff23
-- title:
--   Remainders of $5^{102}$ and $3^{104}$ upon division by $103$
-- statement:
--   This is Problem 4.118 of N. B. Alfutova and A. V. Ustinov, *Algebra and Number Theory* (MCCME, 2002), Chapter 4, §4 “Theorems of Fermat and Euler”. The problem asks for the remainders upon division by $103$ of the numbers (a) $5^{102}$ and (b) $3^{104}$. The book's answers are $1$ and $9$.
--
--   **Theorem.**
--
--   $$
--   5^{102} \bmod 103 = 1, \qquad 3^{104} \bmod 103 = 9 .
--   $$
--
--   Since $103$ is prime, the exercise illustrates Fermat's little theorem $a^{102}\equiv 1 \pmod{103}$ for $103\nmid a$.
--
--   **Formalization Note** The remainders are computed with natural-number division with remainder (`%`) on $\mathbb N$.
-- source:
--   N. B. Alfutova, A. V. Ustinov, «Алгебра и теория чисел. Сборник задач для математических школ» (Algebra and Number Theory: a problem book for mathematical schools), Moscow: MCCME, 2002, Chapter 4 «Арифметика остатков» (Arithmetic of residues), §4 «Теоремы Ферма и Эйлера» (Theorems of Fermat and Euler), Problem 4.118. Problem text and answer as catalogued on problems.ru, problem 60744: https://problems.ru/view_problem_details_new.php?id=60744

import Mathlib

namespace AlfutovaUstinov

theorem problem_4_118 : 5 ^ 102 % 103 = 1 ∧ 3 ^ 104 % 103 = 9 := by sorry

end AlfutovaUstinov
