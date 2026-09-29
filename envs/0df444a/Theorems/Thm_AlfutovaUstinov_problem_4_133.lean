-- Prove2me | Theorems.Thm_AlfutovaUstinov_problem_4_133
-- name    : AlfutovaUstinov.problem_4_133
-- status  : Proved
-- author  : @evgeth
-- created : 2026-09-28T23:44:26.168135+00:00
-- url     : https://prove2.me/theorems/81602b49-544d-43e2-9190-e82b48c10c6d
-- title:
--   $\varphi(1)+\varphi(p)+\varphi(p^2)+\dots+\varphi(p^\alpha)=p^\alpha$
-- statement:
--   This is Problem 4.133 of N. B. Alfutova and A. V. Ustinov, *Algebra and Number Theory* (MCCME, 2002), Chapter 4, §4 “Theorems of Fermat and Euler”. The problem asks for the value of the sum $\varphi(1)+\varphi(p)+\varphi(p^2)+\dots+\varphi(p^\alpha)$, where $\varphi$ is Euler's function, $p$ is a prime (as in the preceding Problem 4.132) and $\alpha$ is a natural number. The book's answer is $p^{\alpha}$.
--
--   **Theorem.** For every prime $p$ and every $\alpha\in\mathbb N$,
--
--   $$
--   \sum_{i=0}^{\alpha}\varphi\!\left(p^{i}\right)=\varphi(1)+\varphi(p)+\dots+\varphi(p^{\alpha}) = p^{\alpha}.
--   $$
--
--   This is the prime-power case of Gauss's identity $\sum_{d\mid n}\varphi(d)=n$.
--
--   **Formalization Note** Euler's function is `Nat.totient`. The statement is proved for all $\alpha\in\mathbb N$, including $\alpha=0$ (where it reads $\varphi(1)=1$), which contains the book's case $\alpha\ge 1$.
-- source:
--   N. B. Alfutova, A. V. Ustinov, «Алгебра и теория чисел. Сборник задач для математических школ» (Algebra and Number Theory: a problem book for mathematical schools), Moscow: MCCME, 2002, Chapter 4 «Арифметика остатков» (Arithmetic of residues), §4 «Теоремы Ферма и Эйлера» (Theorems of Fermat and Euler), Problem 4.133. Problem text and answer as catalogued on problems.ru, problem 60759: https://problems.ru/view_problem_details_new.php?id=60759

import Mathlib

namespace AlfutovaUstinov

theorem problem_4_133 (p : ℕ) (hp : p.Prime) (α : ℕ) :
    ∑ i ∈ Finset.range (α + 1), Nat.totient (p ^ i) = p ^ α := by sorry

end AlfutovaUstinov
