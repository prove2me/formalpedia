-- Prove2me | Theorems.Thm_AlfutovaUstinov_problem_4_139
-- name    : AlfutovaUstinov.problem_4_139
-- status  : Proved
-- author  : @evgeth
-- created : 2026-09-28T23:44:35.963703+00:00
-- url     : https://prove2.me/theorems/66073da5-6bdb-4123-bd9e-dbb3198ca7f2
-- title:
--   Solving $\varphi(x)=2$, $\varphi(x)=8$, $\varphi(x)=12$ and $\varphi(x)=14$
-- statement:
--   This is Problem 4.139 of N. B. Alfutova and A. V. Ustinov, *Algebra and Number Theory* (MCCME, 2002), Chapter 4, §4 “Theorems of Fermat and Euler”. Here $\varphi$ denotes Euler's function: $\varphi(x)$ is the number of integers among $1,2,\dots,x$ coprime to $x$. The problem asks to solve the equations (a) $\varphi(x)=2$; (b) $\varphi(x)=8$; (c) $\varphi(x)=12$; (d) $\varphi(x)=14$ in natural numbers $x$. The book's answers are recorded below.
--
--   **Theorem.** The complete sets of natural solutions are
--
--   1. $\varphi(x)=2 \iff x\in\{3,\,4,\,6\}$;
--   2. $\varphi(x)=8 \iff x\in\{15,\,16,\,20,\,24,\,30\}$;
--   3. $\varphi(x)=12 \iff x\in\{13,\,21,\,26,\,28,\,36,\,42\}$;
--   4. $$\varphi(x)=14 \ \text{ has no solutions.}$$
--
--   Part 4 shows that $14$ is a *nontotient*: an even number that is not a value of Euler's function.
--
--   **Formalization Note** Euler's function is `Nat.totient`; each part is stated as an equality of subsets of $\mathbb N$. Mathlib's convention $\varphi(0)=0$ means that $x=0$ never solves these equations, so quantifying over all of $\mathbb N$ agrees with the book's natural numbers $x\ge1$.
-- source:
--   N. B. Alfutova, A. V. Ustinov, «Алгебра и теория чисел. Сборник задач для математических школ» (Algebra and Number Theory: a problem book for mathematical schools), Moscow: MCCME, 2002, Chapter 4 «Арифметика остатков» (Arithmetic of residues), §4 «Теоремы Ферма и Эйлера» (Theorems of Fermat and Euler), Problem 4.139. Problem text and answer as catalogued on problems.ru, problem 60765: https://problems.ru/view_problem_details_new.php?id=60765

import Mathlib

namespace AlfutovaUstinov

theorem problem_4_139 :
    {x : ℕ | Nat.totient x = 2} = {3, 4, 6} ∧
      {x : ℕ | Nat.totient x = 8} = {15, 16, 20, 24, 30} ∧
      {x : ℕ | Nat.totient x = 12} = {13, 21, 26, 28, 36, 42} ∧
      {x : ℕ | Nat.totient x = 14} = ∅ := by sorry

end AlfutovaUstinov
