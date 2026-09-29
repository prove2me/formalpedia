-- Prove2me | Theorems.Thm_AlfutovaUstinov_problem_4_128
-- name    : AlfutovaUstinov.problem_4_128
-- status  : Proved
-- author  : @evgeth
-- created : 2026-09-28T23:44:31.586601+00:00
-- url     : https://prove2.me/theorems/1de84126-878a-46dd-a2a4-9458d4f38573
-- title:
--   For a prime $p=4k+1$, the numbers $x=\pm(2k)!$ solve $x^2+1\equiv 0 \pmod p$
-- statement:
--   This is Problem 4.128 of N. B. Alfutova and A. V. Ustinov, *Algebra and Number Theory* (MCCME, 2002), Chapter 4, §4 “Theorems of Fermat and Euler”.
--
--   **Theorem.** Let $p$ be a prime of the form $p=4k+1$ with $k\in\mathbb N$. Then both numbers $x=(2k)!$ and $x=-(2k)!$ are solutions of the congruence
--
--   $$
--   x^{2}+1\equiv 0 \pmod p .
--   $$
--
--   This gives an explicit square root of $-1$ modulo every prime $p\equiv 1 \pmod 4$, complementing Problem 4.126, which shows that no such square root exists for primes $p\equiv 3 \pmod 4$. It is a consequence of Wilson's theorem.
--
--   **Formalization Note** The factorial is `Nat.factorial`, cast to $\mathbb Z$; the two claims (for $+(2k)!$ and $-(2k)!$) are stated separately as congruences in $\mathbb Z$ (`Int.ModEq`).
-- source:
--   N. B. Alfutova, A. V. Ustinov, «Алгебра и теория чисел. Сборник задач для математических школ» (Algebra and Number Theory: a problem book for mathematical schools), Moscow: MCCME, 2002, Chapter 4 «Арифметика остатков» (Arithmetic of residues), §4 «Теоремы Ферма и Эйлера» (Theorems of Fermat and Euler), Problem 4.128. Problem text and answer as catalogued on problems.ru, problem 60754: https://problems.ru/view_problem_details_new.php?id=60754

import Mathlib

namespace AlfutovaUstinov

theorem problem_4_128 (p k : ℕ) (hp : p.Prime) (hpk : p = 4 * k + 1) :
    (Nat.factorial (2 * k) : ℤ) ^ 2 + 1 ≡ 0 [ZMOD p] ∧
      (-(Nat.factorial (2 * k) : ℤ)) ^ 2 + 1 ≡ 0 [ZMOD p] := by sorry

end AlfutovaUstinov
