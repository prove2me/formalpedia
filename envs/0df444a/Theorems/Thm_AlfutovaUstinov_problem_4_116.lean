-- Prove2me | Theorems.Thm_AlfutovaUstinov_problem_4_116
-- name    : AlfutovaUstinov.problem_4_116
-- status  : Proved
-- author  : @evgeth
-- created : 2026-09-28T23:43:35.472524+00:00
-- url     : https://prove2.me/theorems/0fd9bc24-001a-4b44-ae30-62dd2433c158
-- title:
--   If $13\mid a^{12}+b^{12}+c^{12}+d^{12}+e^{12}+f^{12}$, then $13^6\mid abcdef$
-- statement:
--   This is Problem 4.116 of N. B. Alfutova and A. V. Ustinov, *Algebra and Number Theory* (MCCME, 2002), Chapter 4, §4 “Theorems of Fermat and Euler”.
--
--   **Theorem.** Let $a,b,c,d,e,f$ be integers such that
--
--   $$
--   13 \mid a^{12}+b^{12}+c^{12}+d^{12}+e^{12}+f^{12}.
--   $$
--
--   Then
--
--   $$
--   13^{6} \mid abcdef .
--   $$
--
--   The statement is an olympiad-style consequence of Fermat's little theorem for the prime $13$: twelfth powers take very few values modulo $13$.
--
--   **Formalization Note** All six variables are integers ($\mathbb Z$), as in the book, and divisibility is the usual divisibility relation on $\mathbb Z$.
-- source:
--   N. B. Alfutova, A. V. Ustinov, «Алгебра и теория чисел. Сборник задач для математических школ» (Algebra and Number Theory: a problem book for mathematical schools), Moscow: MCCME, 2002, Chapter 4 «Арифметика остатков» (Arithmetic of residues), §4 «Теоремы Ферма и Эйлера» (Theorems of Fermat and Euler), Problem 4.116. Problem text and answer as catalogued on problems.ru, problem 60742: https://problems.ru/view_problem_details_new.php?id=60742

import Mathlib

namespace AlfutovaUstinov

theorem problem_4_116 (a b c d e f : ℤ)
    (h : 13 ∣ a ^ 12 + b ^ 12 + c ^ 12 + d ^ 12 + e ^ 12 + f ^ 12) :
    13 ^ 6 ∣ a * b * c * d * e * f := by sorry

end AlfutovaUstinov
