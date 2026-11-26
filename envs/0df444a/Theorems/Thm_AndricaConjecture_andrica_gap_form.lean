-- Prove2me | Theorems.Thm_AndricaConjecture_andrica_gap_form
-- name    : AndricaConjecture.andrica_gap_form
-- status  : Open
-- author  : @fangshuming
-- created : 2026-11-26T09:22:46.789676+00:00
-- url     : https://prove2.me/theorems/504930a1-1114-5110-9618-334bdb5cf1a0
-- title:
--   Equivalent form: $p_{n+1}-p_n<2\sqrt{p_n}+1$
-- statement:
--   Let $p_n$ denote the $n$th prime in Mathlib's zero-based indexing, so that $p_0=2$, $p_1=3$, and $p_n=$ `Nat.nth Nat.Prime n`. Then for every natural number $n$,
--   $$
--   p_{n+1}-p_n < 2\sqrt{p_n}+1,
--   $$
--   where the square root is the real square root and the left-hand side is viewed as a real number. This inequality is equivalent to Andrica's conjecture $\sqrt{p_{n+1}}-\sqrt{p_n}<1$, and is recorded here as a working form rather than as an independent open statement.
-- source:
--   Equivalent algebraic form of Andrica's conjecture; cf. Matt Visser, Variants on Andrica's conjecture with and without the Riemann hypothesis, Mathematics 6 (2018), no. 12, 289, equation (6.1), https://arxiv.org/abs/1804.02500

import Mathlib

namespace AndricaConjecture
theorem andrica_gap_form (n : Nat) :
    (Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n : Real) <
      2 * Real.sqrt (Nat.nth Nat.Prime n : Real) + 1 := by sorry
end AndricaConjecture
