-- Prove2me | Theorems.Thm_AlfutovaUstinov_problem_4_130
-- name    : AlfutovaUstinov.problem_4_130
-- status  : Proved
-- author  : @evgeth
-- created : 2026-09-28T23:44:11.813025+00:00
-- url     : https://prove2.me/theorems/71f835f9-3468-434f-8472-b0565c80cc2e
-- title:
--   Solvability of $x^2+x+1\equiv 0 \pmod p$ implies $p\equiv 1 \pmod 6$; infinitely many primes $6k+1$
-- statement:
--   This is Problem 4.130 of N. B. Alfutova and A. V. Ustinov, *Algebra and Number Theory* (MCCME, 2002), Chapter 4, §4 “Theorems of Fermat and Euler”. The problem has two parts.
--
--   1. Let $p>3$ be a prime. If the congruence
--   $$
--   x^{2}+x+1\equiv 0 \pmod p
--   $$
--   has an integer solution $x$, then $p\equiv 1 \pmod 6$.
--
--   2. There are infinitely many primes of the form $6k+1$, $k\in\mathbb N$ (the book asks to deduce this from part 1).
--
--   Part 1 describes the primes dividing values of the cyclotomic polynomial $\Phi_3(x)=x^2+x+1$, and part 2 is a special case of Dirichlet's theorem on primes in arithmetic progressions.
--
--   **Formalization Note** Part 1 quantifies over natural numbers $p$ with `Nat.Prime p` and $3<p$, with the solution $x$ taken in $\mathbb Z$ and the congruence expressed with `Int.ModEq`; its conclusion uses `Nat.ModEq`. Part 2 states that the set of primes $p$ with $p=6k+1$ for some $k\in\mathbb N$ is infinite.
-- source:
--   N. B. Alfutova, A. V. Ustinov, «Алгебра и теория чисел. Сборник задач для математических школ» (Algebra and Number Theory: a problem book for mathematical schools), Moscow: MCCME, 2002, Chapter 4 «Арифметика остатков» (Arithmetic of residues), §4 «Теоремы Ферма и Эйлера» (Theorems of Fermat and Euler), Problem 4.130. Problem text and answer as catalogued on problems.ru, problem 60756: https://problems.ru/view_problem_details_new.php?id=60756

import Mathlib

namespace AlfutovaUstinov

theorem problem_4_130 :
    (∀ p : ℕ, p.Prime → 3 < p → (∃ x : ℤ, x ^ 2 + x + 1 ≡ 0 [ZMOD p]) → p ≡ 1 [MOD 6]) ∧
      {p : ℕ | p.Prime ∧ ∃ k : ℕ, p = 6 * k + 1}.Infinite := by sorry

end AlfutovaUstinov
