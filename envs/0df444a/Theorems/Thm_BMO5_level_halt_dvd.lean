-- Prove2me | Theorems.Thm_BMO5_level_halt_dvd
-- name    : BMO5.level_halt_dvd
-- status  : Proved
-- author  : @alon yuval
-- created : 2026-11-23T16:40:54.96401+00:00
-- url     : https://prove2.me/theorems/09c8ec85-ac00-4ee9-b136-a8105c79d248
-- title:
--   BMO #5: halting inside a level forces $3^k \mid 20\cdot 2^i + i + 1$
-- statement:
--   In Beaver Math Olympiad problem 5 the state is a pair $(a_n, b_n)$ with $f(x) = 10\cdot 2^x - 1$. While $b_n < f(a_n)$ the level $i = a_n$ is fixed and $b$ evolves by the affine map $T_i(b) = 3b + i + 5$; the machine halts exactly when $b = f(i) - 1 = 10\cdot 2^i - 2$.
--
--   **Theorem.** For all $i, b, k \in \mathbb N$, if $T_i^{k}(b) = 10\cdot 2^i - 2$ then
--   $$3^k \mid 20\cdot 2^i + i + 1.$$
--
--   The point is the conjugation $c = 2b + i + 5$, under which $T_i$ becomes $c \mapsto 3c$: one has $2T_i^k(b) + i + 5 = 3^k(2b + i + 5)$, so halting after $k$ triplings at level $i$ is equivalent to the Diophantine equation $3^k(2b + i + 5) = 20\cdot 2^i + i + 1$. In these coordinates the whole problem reads: multiply by $3$ until passing roughly $20\cdot 2^i$, subtract $20\cdot 2^i - 3$, and move to level $i+1$ — a $2$-versus-$3$ problem in the spirit of Mahler's $3/2$ problem.
-- source:
--   Beaver Math Olympiad problem 5, https://wiki.bbchallenge.org/wiki/Beaver_Math_Olympiad (machine 1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_---0RE); formal-conjectures FormalConjectures/Other/BeaverMathOlympiad.lean, beaver_math_olympiad_problem_5. The conjugation c = 2b + i + 5 is an original observation of this submission.

import Mathlib

namespace BMO5
theorem level_halt_dvd (i b k : ℕ)
    (h : (fun x => 3 * x + i + 5)^[k] b = 10 * 2 ^ i - 2) :
    3 ^ k ∣ 20 * 2 ^ i + i + 1 := by
  sorry
end BMO5
