-- Prove2me | Theorems.Thm_AlfutovaUstinov_problem_4_112
-- name    : AlfutovaUstinov.problem_4_112
-- status  : Proved
-- author  : @evgeth
-- created : 2026-09-28T23:43:25.485999+00:00
-- url     : https://prove2.me/theorems/689b19c6-f008-457e-8a35-3be86ff8e950
-- title:
--   For which $n$ is $n^{2001}-n^{4}$ divisible by $11$?
-- statement:
--   This is Problem 4.112 of N. B. Alfutova and A. V. Ustinov, *Algebra and Number Theory* (MCCME, 2002), Chapter 4, §4 “Theorems of Fermat and Euler”. The problem asks: for which $n$ is the number $n^{2001}-n^{4}$ divisible by $11$? The book's answer is: exactly for $n\equiv 0$ and $n\equiv 1 \pmod{11}$.
--
--   **Theorem.** For every integer $n$,
--
--   $$
--   11 \mid n^{2001}-n^{4} \iff n\equiv 0 \pmod{11}\ \text{ or }\ n\equiv 1 \pmod{11}.
--   $$
--
--   This is a typical exercise on reducing a large exponent modulo a prime by means of Fermat's little theorem.
--
--   **Formalization Note** The variable $n$ ranges over all integers $\mathbb Z$, and the congruences are expressed with `Int.ModEq` (notation `n ≡ a [ZMOD 11]`).
-- source:
--   N. B. Alfutova, A. V. Ustinov, «Алгебра и теория чисел. Сборник задач для математических школ» (Algebra and Number Theory: a problem book for mathematical schools), Moscow: MCCME, 2002, Chapter 4 «Арифметика остатков» (Arithmetic of residues), §4 «Теоремы Ферма и Эйлера» (Theorems of Fermat and Euler), Problem 4.112. Problem text and answer as catalogued on problems.ru, problem 60738: https://problems.ru/view_problem_details_new.php?id=60738

import Mathlib

namespace AlfutovaUstinov

theorem problem_4_112 (n : ℤ) : 11 ∣ n ^ 2001 - n ^ 4 ↔ n ≡ 0 [ZMOD 11] ∨ n ≡ 1 [ZMOD 11] := by sorry

end AlfutovaUstinov
