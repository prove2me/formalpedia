-- Prove2me | Theorems.Thm_AlfutovaUstinov_problem_4_141
-- name    : AlfutovaUstinov.problem_4_141
-- status  : Proved
-- author  : @evgeth
-- created : 2026-09-28T23:44:38.517194+00:00
-- url     : https://prove2.me/theorems/8d6ad7f3-4d25-4ff3-8ce2-6296711fd3aa
-- title:
--   Solving $\varphi(x)=x/2$, $\varphi(x)=x/3$ and $\varphi(x)=x/4$
-- statement:
--   This is Problem 4.141 of N. B. Alfutova and A. V. Ustinov, *Algebra and Number Theory* (MCCME, 2002), Chapter 4, §4 “Theorems of Fermat and Euler”. Here $\varphi$ is Euler's function. The problem asks to solve, in natural numbers $x$, the equations (a) $\varphi(x)=x/2$; (b) $\varphi(x)=x/3$; (c) $\varphi(x)=x/4$. The book's answers: (a) $x=2^{\alpha}$; (b) $x=2^{\alpha}3^{\beta}$ with $\alpha,\beta\ge1$; (c) no solutions.
--
--   **Theorem.** For natural numbers $x\ge1$:
--
--   1. $\varphi(x)=\dfrac{x}{2}$ if and only if $x=2^{\alpha}$ for some integer $\alpha\ge1$;
--   2. $\varphi(x)=\dfrac{x}{3}$ if and only if $x=2^{\alpha}3^{\beta}$ for some integers $\alpha\ge1$, $\beta\ge1$;
--   3. $$\varphi(x)=\frac{x}{4}\ \text{ has no solutions.}$$
--
--   The problem illustrates the product formula $\varphi(x)/x=\prod_{p\mid x}(1-1/p)$: the ratio $\varphi(x)/x$ depends only on the set of prime divisors of $x$.
--
--   **Formalization Note** Euler's function is `Nat.totient`. Each equation $\varphi(x)=x/c$ is written without division as $c\cdot\varphi(x)=x$, which is equivalent for natural numbers; the solution sets are stated as equalities of subsets of $\mathbb N$, restricted to $x>0$.
-- source:
--   N. B. Alfutova, A. V. Ustinov, «Алгебра и теория чисел. Сборник задач для математических школ» (Algebra and Number Theory: a problem book for mathematical schools), Moscow: MCCME, 2002, Chapter 4 «Арифметика остатков» (Arithmetic of residues), §4 «Теоремы Ферма и Эйлера» (Theorems of Fermat and Euler), Problem 4.141. Problem text and answer as catalogued on problems.ru, problem 60767: https://problems.ru/view_problem_details_new.php?id=60767

import Mathlib

namespace AlfutovaUstinov

theorem problem_4_141 :
    {x : ℕ | 0 < x ∧ 2 * Nat.totient x = x} = {x | ∃ α : ℕ, 0 < α ∧ x = 2 ^ α} ∧
      {x : ℕ | 0 < x ∧ 3 * Nat.totient x = x} =
        {x | ∃ α β : ℕ, 0 < α ∧ 0 < β ∧ x = 2 ^ α * 3 ^ β} ∧
      {x : ℕ | 0 < x ∧ 4 * Nat.totient x = x} = ∅ := by sorry

end AlfutovaUstinov
