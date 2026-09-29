-- Prove2me | Theorems.Thm_AlfutovaUstinov_problem_4_119
-- name    : AlfutovaUstinov.problem_4_119
-- status  : Proved
-- author  : @evgeth
-- created : 2026-09-28T23:43:41.578413+00:00
-- url     : https://prove2.me/theorems/00f0050b-a0b7-40bd-8ddc-d58fa2abf50e
-- title:
--   The number $30^{239}+239^{30}$ is composite
-- statement:
--   This is Problem 4.119 of N. B. Alfutova and A. V. Ustinov, *Algebra and Number Theory* (MCCME, 2002), Chapter 4, §4 “Theorems of Fermat and Euler”.
--
--   **Theorem.** The natural number
--
--   $$
--   N = 30^{239}+239^{30}
--   $$
--
--   is composite, i.e. $N>1$ and $N$ is not prime.
--
--   The exercise is a classical application of Fermat's little theorem to exhibit an explicit small prime factor of a huge number.
--
--   **Formalization Note** “Composite” is formalized as the conjunction $1<N$ and $\neg\,\mathrm{Prime}(N)$ for the natural number $N$ (`Nat.Prime`).
-- source:
--   N. B. Alfutova, A. V. Ustinov, «Алгебра и теория чисел. Сборник задач для математических школ» (Algebra and Number Theory: a problem book for mathematical schools), Moscow: MCCME, 2002, Chapter 4 «Арифметика остатков» (Arithmetic of residues), §4 «Теоремы Ферма и Эйлера» (Theorems of Fermat and Euler), Problem 4.119. Problem text and answer as catalogued on problems.ru, problem 30678: https://problems.ru/view_problem_details_new.php?id=30678

import Mathlib

namespace AlfutovaUstinov

theorem problem_4_119 : 1 < 30 ^ 239 + 239 ^ 30 ∧ ¬ Nat.Prime (30 ^ 239 + 239 ^ 30) := by sorry

end AlfutovaUstinov
