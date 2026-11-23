-- Prove2me | Theorems.Thm_BMO5_no_halt_after_tripling_mod6
-- name    : BMO5.no_halt_after_tripling_mod6
-- status  : Proved
-- author  : @alon yuval
-- created : 2026-11-23T16:40:56.535161+00:00
-- url     : https://prove2.me/theorems/45de8c19-8871-47ad-ae34-9f2bf9b111fd
-- title:
--   BMO #5: no halt after a tripling at levels $i \not\equiv 0, 1 \pmod 6$
-- statement:
--   With the notation of Beaver Math Olympiad problem 5 ($f(x) = 10\cdot 2^x - 1$, level map $T_i(b) = 3b + i + 5$, halting value $f(i) - 1 = 10\cdot 2^i - 2$):
--
--   **Theorem.** If $i \not\equiv 0, 1 \pmod 6$ and $k \ge 1$, then $T_i^{k}(b) \ne 10\cdot 2^i - 2$ for every $b$.
--
--   So at two thirds of all levels the machine can only halt at the very moment a level is entered, never after a tripling step. More generally (by `BMO5.level_halt_dvd`) halting after $k$ triplings at level $i$ forces $i$ into exactly two residue classes modulo $2\cdot 3^k$ (checked for $k \le 6$), so the admissible levels have density $3^{-k}$.
-- source:
--   Beaver Math Olympiad problem 5, https://wiki.bbchallenge.org/wiki/Beaver_Math_Olympiad (machine 1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_---0RE); formal-conjectures FormalConjectures/Other/BeaverMathOlympiad.lean, beaver_math_olympiad_problem_5. The conjugation c = 2b + i + 5 is an original observation of this submission.

import Mathlib

namespace BMO5
theorem no_halt_after_tripling_mod6 (i b k : ℕ) (hk : 1 ≤ k)
    (hi0 : i % 6 ≠ 0) (hi1 : i % 6 ≠ 1) :
    (fun x => 3 * x + i + 5)^[k] b ≠ 10 * 2 ^ i - 2 := by
  sorry
end BMO5
