-- Prove2me | Theorems.Thm_AlfutovaUstinov_problem_4_120
-- name    : AlfutovaUstinov.problem_4_120
-- status  : Proved
-- author  : @evgeth
-- created : 2026-09-28T23:43:49.370297+00:00
-- url     : https://prove2.me/theorems/41950e3c-b954-4f56-9467-d03d9c71dff6
-- title:
--   Is $257^{1092}+1092$ prime? (No.)
-- statement:
--   This is Problem 4.120 of N. B. Alfutova and A. V. Ustinov, *Algebra and Number Theory* (MCCME, 2002), Chapter 4, §4 “Theorems of Fermat and Euler”. The problem asks whether the number $257^{1092}+1092$ is prime; the book's answer is that it is not.
--
--   **Theorem.** The natural number
--
--   $$
--   257^{1092}+1092
--   $$
--
--   is not prime.
--
--   Like the neighbouring exercises, this illustrates how Fermat's little theorem reveals a divisor of a number far too large to factor by hand.
--
--   **Formalization Note** Primality is `Nat.Prime` on $\mathbb N$.
-- source:
--   N. B. Alfutova, A. V. Ustinov, «Алгебра и теория чисел. Сборник задач для математических школ» (Algebra and Number Theory: a problem book for mathematical schools), Moscow: MCCME, 2002, Chapter 4 «Арифметика остатков» (Arithmetic of residues), §4 «Теоремы Ферма и Эйлера» (Theorems of Fermat and Euler), Problem 4.120. Problem text and answer as catalogued on problems.ru, problem 60746: https://problems.ru/view_problem_details_new.php?id=60746

import Mathlib

namespace AlfutovaUstinov

theorem problem_4_120 : ¬ Nat.Prime (257 ^ 1092 + 1092) := by sorry

end AlfutovaUstinov
