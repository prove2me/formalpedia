-- Prove2me | Theorems.Thm_AlfutovaUstinov_problem_4_127
-- name    : AlfutovaUstinov.problem_4_127
-- status  : Proved
-- author  : @evgeth
-- created : 2026-09-28T23:44:08.444362+00:00
-- url     : https://prove2.me/theorems/7227fd29-a5e1-43ff-8cf6-200f489c57a2
-- title:
--   There are infinitely many primes of the form $4k+1$
-- statement:
--   This is Problem 4.127 of N. B. Alfutova and A. V. Ustinov, *Algebra and Number Theory* (MCCME, 2002), Chapter 4, §4 “Theorems of Fermat and Euler”. (In the book the problem is to be solved with the help of the preceding Problem 4.126.)
--
--   **Theorem.** There are infinitely many prime numbers of the form
--
--   $$
--   p = 4k+1, \qquad k\in\mathbb N .
--   $$
--
--   This is the simplest nontrivial special case of Dirichlet's theorem on primes in arithmetic progressions, and it admits an elementary Euclid-style proof.
--
--   **Formalization Note** The statement says that the set $\{p\in\mathbb N : p \text{ is prime and } p=4k+1 \text{ for some } k\in\mathbb N\}$ is infinite (`Set.Infinite`).
-- source:
--   N. B. Alfutova, A. V. Ustinov, «Алгебра и теория чисел. Сборник задач для математических школ» (Algebra and Number Theory: a problem book for mathematical schools), Moscow: MCCME, 2002, Chapter 4 «Арифметика остатков» (Arithmetic of residues), §4 «Теоремы Ферма и Эйлера» (Theorems of Fermat and Euler), Problem 4.127. Problem text and answer as catalogued on problems.ru, problem 60753: https://problems.ru/view_problem_details_new.php?id=60753

import Mathlib

namespace AlfutovaUstinov

theorem problem_4_127 : {p : ℕ | p.Prime ∧ ∃ k : ℕ, p = 4 * k + 1}.Infinite := by sorry

end AlfutovaUstinov
