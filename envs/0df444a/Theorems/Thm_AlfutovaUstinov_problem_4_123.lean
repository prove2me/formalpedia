-- Prove2me | Theorems.Thm_AlfutovaUstinov_problem_4_123
-- name    : AlfutovaUstinov.problem_4_123
-- status  : Proved
-- author  : @evgeth
-- created : 2026-09-28T23:43:54.901916+00:00
-- url     : https://prove2.me/theorems/474fcc6a-f9f6-441b-949c-812fb64fce5c
-- title:
--   If $17\nmid n$, then $17$ divides $n^8+1$ or $n^8-1$
-- statement:
--   This is Problem 4.123 of N. B. Alfutova and A. V. Ustinov, *Algebra and Number Theory* (MCCME, 2002), Chapter 4, §4 “Theorems of Fermat and Euler”.
--
--   **Theorem.** Let $n$ be a natural number that is not divisible by $17$. Then
--
--   $$
--   17 \mid n^{8}+1 \quad\text{or}\quad 17 \mid n^{8}-1 .
--   $$
--
--   This is a direct application of Fermat's little theorem for the prime $17$, where $17-1=16=2\cdot 8$.
--
--   **Formalization Note** The number $n$ is a natural number, as in the book. The expression $n^8-1$ uses natural-number subtraction, which is exact here: the hypothesis $17\nmid n$ forces $n\ge1$, hence $n^8\ge1$.
-- source:
--   N. B. Alfutova, A. V. Ustinov, «Алгебра и теория чисел. Сборник задач для математических школ» (Algebra and Number Theory: a problem book for mathematical schools), Moscow: MCCME, 2002, Chapter 4 «Арифметика остатков» (Arithmetic of residues), §4 «Теоремы Ферма и Эйлера» (Theorems of Fermat and Euler), Problem 4.123. Problem text and answer as catalogued on problems.ru, problem 60749: https://problems.ru/view_problem_details_new.php?id=60749

import Mathlib

namespace AlfutovaUstinov

theorem problem_4_123 (n : ℕ) (hn : ¬ 17 ∣ n) : 17 ∣ n ^ 8 + 1 ∨ 17 ∣ n ^ 8 - 1 := by sorry

end AlfutovaUstinov
