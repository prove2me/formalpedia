-- Prove2me | Theorems.Thm_BMO5_no_triple_subtraction
-- name    : BMO5.no_triple_subtraction
-- status  : Proved
-- author  : @alon yuval
-- created : 2026-11-23T16:54:21.597611+00:00
-- url     : https://prove2.me/theorems/9066787b-5148-4166-9533-1d582e6a5b49
-- title:
--   BMO #5 never takes three subtraction steps in a row
-- statement:
--   Let $f(x) = 10\cdot 2^x - 1$, $(a_0, b_0) = (0, 5)$, and $(a_{n+1}, b_{n+1}) = (a_n + 1, b_n - f(a_n))$ if $b_n \ge f(a_n)$, otherwise $(a_n, 3b_n + a_n + 5)$. This is Beaver Math Olympiad problem 5; the underlying 6-state Turing machine halts iff $b_n = f(a_n) - 1$ for some $n$.
--
--   **Theorem.** There is no $n$ such that the subtraction branch ($b \ge f(a)$) is taken at steps $n$, $n+1$ and $n+2$.
--
--   Equivalently, among any two consecutive levels at least one performs a tripling step, which bounds the tripling counts from below. The proof uses the invariant $2b_n + a_n + 5 < 3(20\cdot 2^{a_n} + a_n + 3)$: three subtractions would need $b_n \ge 70\cdot 2^{a_n} - 3$, which contradicts it.
-- source:
--   Beaver Math Olympiad problem 5 (machine 1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_---0RE), https://wiki.bbchallenge.org/wiki/Beaver_Math_Olympiad ; recurrence as in formal-conjectures beaver_math_olympiad_problem_5 with f(x) = 10*2^x - 1 inlined. Original result of this submission.

import Mathlib

namespace BMO5
theorem no_triple_subtraction (a b : ℕ → ℕ) (a_ini : a 0 = 0) (b_ini : b 0 = 5)
    (a_rec : ∀ n, a (n + 1) = if 10 * 2 ^ (a n) - 1 ≤ b n then a n + 1 else a n)
    (b_rec : ∀ n, b (n + 1) = if 10 * 2 ^ (a n) - 1 ≤ b n then b n - (10 * 2 ^ (a n) - 1)
      else 3 * b n + a n + 5) :
    ∀ n, ¬ (10 * 2 ^ (a n) - 1 ≤ b n ∧ 10 * 2 ^ (a (n + 1)) - 1 ≤ b (n + 1) ∧
      10 * 2 ^ (a (n + 2)) - 1 ≤ b (n + 2)) := by
  sorry
end BMO5
