-- Prove2me | Theorems.Thm_AlfutovaUstinov_problem_4_108
-- name    : AlfutovaUstinov.problem_4_108
-- status  : Proved
-- author  : @evgeth
-- created : 2026-09-28T23:43:12.251+00:00
-- url     : https://prove2.me/theorems/1430048e-d56e-4301-b717-063addd2d407
-- title:
--   Divisibility of $10^n-1$ by $7$, $13$, $91$ and $819$
-- statement:
--   This is Problem 4.108 of N. B. Alfutova and A. V. Ustinov, *Algebra and Number Theory* (MCCME, 2002), Chapter 4, §4 “Theorems of Fermat and Euler”. The problem asks for an exponent $n$ such that $10^n-1$ is divisible by (a) $7$, (b) $13$, (c) $91$, (d) $819$; the book's answer is $n=6$.
--
--   The formal statement records the complete answer. For every natural number $n$ and for each modulus $d\in\{7,\,13,\,91,\,819\}$,
--
--   $$
--   d \mid 10^{n}-1 \iff 6 \mid n .
--   $$
--
--   In particular $n=6$ is the smallest positive exponent that works in all four cases (note $91=7\cdot 13$ and $819=9\cdot 7\cdot 13$).
--
--   The exercise concerns the multiplicative order of $10$ modulo small primes, which governs the period length of decimal fractions such as $1/7$ and $1/13$.
--
--   **Formalization Note** The four parts are combined into one conjunction of equivalences, quantified over all $n\in\mathbb N$ (the case $n=0$ is harmless: $10^0-1=0$ is divisible by everything and $6\mid 0$). The subtraction $10^n-1$ is natural-number subtraction, which is exact because $10^n\ge 1$.
-- source:
--   N. B. Alfutova, A. V. Ustinov, «Алгебра и теория чисел. Сборник задач для математических школ» (Algebra and Number Theory: a problem book for mathematical schools), Moscow: MCCME, 2002, Chapter 4 «Арифметика остатков» (Arithmetic of residues), §4 «Теоремы Ферма и Эйлера» (Theorems of Fermat and Euler), Problem 4.108. Problem text and answer as catalogued on problems.ru, problem 60734: https://problems.ru/view_problem_details_new.php?id=60734

import Mathlib

namespace AlfutovaUstinov

theorem problem_4_108 (n : ℕ) :
    (7 ∣ 10 ^ n - 1 ↔ 6 ∣ n) ∧ (13 ∣ 10 ^ n - 1 ↔ 6 ∣ n) ∧
      (91 ∣ 10 ^ n - 1 ↔ 6 ∣ n) ∧ (819 ∣ 10 ^ n - 1 ↔ 6 ∣ n) := by sorry

end AlfutovaUstinov
