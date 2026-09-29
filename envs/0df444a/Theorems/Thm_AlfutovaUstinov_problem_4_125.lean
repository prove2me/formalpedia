-- Prove2me | Theorems.Thm_AlfutovaUstinov_problem_4_125
-- name    : AlfutovaUstinov.problem_4_125
-- status  : Proved
-- author  : @evgeth
-- created : 2026-09-28T23:43:56.307888+00:00
-- url     : https://prove2.me/theorems/b99ed653-470e-46b8-957d-f622d0620df6
-- title:
--   Quadratic residues satisfy $a^{(p-1)/2}\equiv 1 \pmod p$
-- statement:
--   This is Problem 4.125 of N. B. Alfutova and A. V. Ustinov, *Algebra and Number Theory* (MCCME, 2002), Chapter 4, §4 “Theorems of Fermat and Euler”.
--
--   **Theorem.** Let $p>2$ be a prime and let $a$ be an integer not divisible by $p$. Suppose that $a$ is a square modulo $p$, i.e. there is an integer $x$ with
--
--   $$
--   x^{2}\equiv a \pmod p .
--   $$
--
--   Then
--
--   $$
--   a^{\frac{p-1}{2}} \equiv 1 \pmod p .
--   $$
--
--   This is one half of Euler's criterion for quadratic residues; the book uses it to study which primes divide numbers of the form $x^2+1$.
--
--   **Formalization Note** The exponent $(p-1)/2$ is natural-number division, which is exact because $p$ is odd. Congruences are `Int.ModEq` on $\mathbb Z$.
-- source:
--   N. B. Alfutova, A. V. Ustinov, «Алгебра и теория чисел. Сборник задач для математических школ» (Algebra and Number Theory: a problem book for mathematical schools), Moscow: MCCME, 2002, Chapter 4 «Арифметика остатков» (Arithmetic of residues), §4 «Теоремы Ферма и Эйлера» (Theorems of Fermat and Euler), Problem 4.125. Problem text and answer as catalogued on problems.ru, problem 60751: https://problems.ru/view_problem_details_new.php?id=60751

import Mathlib

namespace AlfutovaUstinov

theorem problem_4_125 (p : ℕ) (hp : p.Prime) (hp2 : 2 < p) (a x : ℤ) (ha : ¬ (p : ℤ) ∣ a)
    (hx : x ^ 2 ≡ a [ZMOD p]) : a ^ ((p - 1) / 2) ≡ 1 [ZMOD p] := by sorry

end AlfutovaUstinov
