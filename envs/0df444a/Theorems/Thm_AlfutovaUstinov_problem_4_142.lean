-- Prove2me | Theorems.Thm_AlfutovaUstinov_problem_4_142
-- name    : AlfutovaUstinov.problem_4_142
-- status  : Proved
-- author  : @evgeth
-- created : 2026-09-28T23:44:27.412779+00:00
-- url     : https://prove2.me/theorems/a30c9912-bc80-48b7-8aa0-43d7f1d9e222
-- title:
--   When do $\varphi(n)=n-1$, $\varphi(2n)=2\varphi(n)$ and $\varphi(n^k)=n^{k-1}\varphi(n)$ hold?
-- statement:
--   This is Problem 4.142 of N. B. Alfutova and A. V. Ustinov, *Algebra and Number Theory* (MCCME, 2002), Chapter 4, §4 “Theorems of Fermat and Euler”. The problem asks for which natural numbers $n$ the following equalities are possible, where $\varphi$ is Euler's function: (a) $\varphi(n)=n-1$; (b) $\varphi(2n)=2\varphi(n)$; (c) $\varphi(n^{k})=n^{k-1}\varphi(n)$. The book's answers are: (a) for prime $n$; (b) for even $n$; (c) for every $n$.
--
--   **Theorem.** For natural numbers $n\ge 1$ and $k\ge1$:
--
--   1. $\varphi(n)=n-1$ if and only if $n$ is prime;
--   2. $\varphi(2n)=2\varphi(n)$ if and only if $n$ is even;
--   3. $$\varphi\!\left(n^{k}\right)=n^{k-1}\,\varphi(n)\quad\text{always holds.}$$
--
--   These are standard characterizations and identities for Euler's function, following from its multiplicativity and the product formula.
--
--   **Formalization Note** Euler's function is `Nat.totient`. The natural numbers $n$ (and the exponents $k$ in part 3) are assumed positive, matching the book's setting; $n-1$ and $k-1$ are natural-number subtractions, which are exact under these assumptions.
-- source:
--   N. B. Alfutova, A. V. Ustinov, «Алгебра и теория чисел. Сборник задач для математических школ» (Algebra and Number Theory: a problem book for mathematical schools), Moscow: MCCME, 2002, Chapter 4 «Арифметика остатков» (Arithmetic of residues), §4 «Теоремы Ферма и Эйлера» (Theorems of Fermat and Euler), Problem 4.142. Problem text and answer as catalogued on problems.ru, problem 60768: https://problems.ru/view_problem_details_new.php?id=60768

import Mathlib

namespace AlfutovaUstinov

theorem problem_4_142 :
    (∀ n : ℕ, 0 < n → (Nat.totient n = n - 1 ↔ n.Prime)) ∧
      (∀ n : ℕ, 0 < n → (Nat.totient (2 * n) = 2 * Nat.totient n ↔ Even n)) ∧
      (∀ n k : ℕ, 0 < n → 0 < k → Nat.totient (n ^ k) = n ^ (k - 1) * Nat.totient n) := by sorry

end AlfutovaUstinov
