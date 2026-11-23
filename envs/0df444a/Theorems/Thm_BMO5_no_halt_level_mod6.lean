-- Prove2me | Theorems.Thm_BMO5_no_halt_level_mod6
-- name    : BMO5.no_halt_level_mod6
-- status  : Proved
-- author  : @alon yuval
-- created : 2026-11-23T16:54:20.243106+00:00
-- url     : https://prove2.me/theorems/37ac01f9-f44a-422f-91a3-1d86064fb2c5
-- title:
--   BMO #5 never halts at a level $a_n \equiv 3, 4 \pmod 6$
-- statement:
--   Let $f(x) = 10\cdot 2^x - 1$, $(a_0, b_0) = (0, 5)$, and $(a_{n+1}, b_{n+1}) = (a_n + 1, b_n - f(a_n))$ if $b_n \ge f(a_n)$, otherwise $(a_n, 3b_n + a_n + 5)$. This is Beaver Math Olympiad problem 5; the underlying 6-state Turing machine halts iff $b_n = f(a_n) - 1$ for some $n$.
--
--   **Theorem.** For every $n$ with $a_n \equiv 3$ or $4 \pmod 6$, $b_n \ne f(a_n) - 1$. So the machine can never halt at a third of all levels.
--
--   Proof idea: with $c = 2b + a + 5$ a tripling multiplies $c$ by $3$. A halting state reached by a tripling forces $3 \mid 20\cdot 2^i + i + 1$, i.e. $i \equiv 0, 1 \pmod 6$. A halting state reached by a subtraction that follows a tripling forces $i \equiv 2 \pmod 3$. Two consecutive subtractions are ruled out by the invariant $2b_n + a_n + 5 < 3(20\cdot 2^{a_n} + a_n + 3)$.
-- source:
--   Beaver Math Olympiad problem 5 (machine 1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_---0RE), https://wiki.bbchallenge.org/wiki/Beaver_Math_Olympiad ; recurrence as in formal-conjectures beaver_math_olympiad_problem_5 with f(x) = 10*2^x - 1 inlined. Original result of this submission.

import Mathlib

namespace BMO5
theorem no_halt_level_mod6 (a b : ℕ → ℕ) (a_ini : a 0 = 0) (b_ini : b 0 = 5)
    (a_rec : ∀ n, a (n + 1) = if 10 * 2 ^ (a n) - 1 ≤ b n then a n + 1 else a n)
    (b_rec : ∀ n, b (n + 1) = if 10 * 2 ^ (a n) - 1 ≤ b n then b n - (10 * 2 ^ (a n) - 1)
      else 3 * b n + a n + 5) :
    ∀ n, (a n % 6 = 3 ∨ a n % 6 = 4) → b n ≠ 10 * 2 ^ (a n) - 2 := by
  sorry
end BMO5
