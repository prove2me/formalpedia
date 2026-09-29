-- Prove2me | Theorems.Thm_AlfutovaUstinov_problem_4_132
-- name    : AlfutovaUstinov.problem_4_132
-- status  : Proved
-- author  : @evgeth
-- created : 2026-09-28T23:44:13.531917+00:00
-- url     : https://prove2.me/theorems/697559d7-a73a-4c52-bc9b-6bad57d7da59
-- title:
--   Values of Euler\'s function: $\varphi(17)$, $\varphi(p)$, $\varphi(p^2)$, $\varphi(p^\alpha)$
-- statement:
--   This is Problem 4.132 of N. B. Alfutova and A. V. Ustinov, *Algebra and Number Theory* (MCCME, 2002), Chapter 4, §4 “Theorems of Fermat and Euler”.
--
--   Euler's function $\varphi(n)$ is the number of integers among $1,2,\dots,n$ that are coprime to $n$. The problem asks for (a) $\varphi(17)$, (b) $\varphi(p)$, (c) $\varphi(p^2)$, (d) $\varphi(p^{\alpha})$, where $p$ is a prime and $\alpha\ge 1$ is a natural number.
--
--   **Theorem.** For every prime $p$ and every integer $\alpha\ge1$:
--
--   1. $\varphi(17)=16$;
--   2. $\varphi(p)=p-1$;
--   3. $\varphi(p^{2})=p(p-1)$;
--   4. $$\varphi(p^{\alpha})=p^{\alpha-1}(p-1).$$
--
--   These values, together with multiplicativity, give the standard product formula for Euler's function.
--
--   **Formalization Note** Euler's function is Mathlib's `Nat.totient`, which counts the $k\in\{0,\dots,n-1\}$ with $\gcd(k,n)=1$; for $n\ge1$ this agrees with the book's definition. The subtractions $p-1$ and $\alpha-1$ are natural-number subtractions, exact because $p\ge 2$ and $\alpha\ge 1$.
-- source:
--   N. B. Alfutova, A. V. Ustinov, «Алгебра и теория чисел. Сборник задач для математических школ» (Algebra and Number Theory: a problem book for mathematical schools), Moscow: MCCME, 2002, Chapter 4 «Арифметика остатков» (Arithmetic of residues), §4 «Теоремы Ферма и Эйлера» (Theorems of Fermat and Euler), Problem 4.132. Problem text and answer as catalogued on problems.ru, problem 60758: https://problems.ru/view_problem_details_new.php?id=60758

import Mathlib

namespace AlfutovaUstinov

theorem problem_4_132 (p : ℕ) (hp : p.Prime) (α : ℕ) (hα : 0 < α) :
    Nat.totient 17 = 16 ∧ Nat.totient p = p - 1 ∧ Nat.totient (p ^ 2) = p * (p - 1) ∧
      Nat.totient (p ^ α) = p ^ (α - 1) * (p - 1) := by sorry

end AlfutovaUstinov
