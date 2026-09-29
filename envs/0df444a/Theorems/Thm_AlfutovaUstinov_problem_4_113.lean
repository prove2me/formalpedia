-- Prove2me | Theorems.Thm_AlfutovaUstinov_problem_4_113
-- name    : AlfutovaUstinov.problem_4_113
-- status  : Proved
-- author  : @evgeth
-- created : 2026-09-28T23:44:24.521699+00:00
-- url     : https://prove2.me/theorems/a1cafd42-a16f-4392-953f-f5b49f9bb770
-- title:
--   Every natural number has a multiple written with the digits $0$ and $1$ only
-- statement:
--   This is Problem 4.113 of N. B. Alfutova and A. V. Ustinov, *Algebra and Number Theory* (MCCME, 2002), Chapter 4, §4 “Theorems of Fermat and Euler”.
--
--   **Theorem.** For every natural number $n\ge 1$ there is a positive multiple $m$ of $n$ whose decimal representation consists only of the digits $0$ and $1$:
--
--   $$
--   \exists\, m\ge 1:\qquad n\mid m \quad\text{and every decimal digit of } m \text{ is } 0 \text{ or } 1 .
--   $$
--
--   This is a classical pigeonhole-principle exercise; it shows, for instance, that $1/n$ can be approximated arbitrarily well by decimal fractions built from zeros and ones.
--
--   **Formalization Note** The decimal digits of $m$ are Mathlib's `Nat.digits 10 m` (the list of base-$10$ digits, least significant first, without leading zeros). The multiple $m$ is required to be positive, which excludes the trivial multiple $0$.
-- source:
--   N. B. Alfutova, A. V. Ustinov, «Алгебра и теория чисел. Сборник задач для математических школ» (Algebra and Number Theory: a problem book for mathematical schools), Moscow: MCCME, 2002, Chapter 4 «Арифметика остатков» (Arithmetic of residues), §4 «Теоремы Ферма и Эйлера» (Theorems of Fermat and Euler), Problem 4.113. Problem text and answer as catalogued on problems.ru, problem 60739: https://problems.ru/view_problem_details_new.php?id=60739

import Mathlib

namespace AlfutovaUstinov

theorem problem_4_113 (n : ℕ) (hn : 0 < n) :
    ∃ m : ℕ, 0 < m ∧ n ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 := by sorry

end AlfutovaUstinov
