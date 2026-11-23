-- Prove2me | Theorems.Thm_BMO5_three_adic_existence
-- name    : BMO5.three_adic_existence
-- status  : Proved
-- author  : @alon yuval
-- created : 2026-11-23T16:57:46.170875+00:00
-- url     : https://prove2.me/theorems/4581a407-9ad9-41b6-b5df-9d157cd6a532
-- title:
--   BMO #5: for each parity some level satisfies $3^k \mid 20\cdot 2^i + i + 1$
-- statement:
--   Let $g(i) = 20\cdot 2^i + i + 1$. **Theorem.** For every $k$ and each parity $r \in \{0,1\}$ there is $i \equiv r \pmod 2$ with $3^k \mid g(i)$.
--
--   Together with `BMO5.three_adic_uniqueness` this shows that $\{i : 3^k \mid g(i)\}$ is exactly two residue classes modulo $2\cdot 3^k$, one of each parity. By `BMO5.level_halt_dvd` these are the only levels where Beaver Math Olympiad problem 5 can halt after $k$ tripling steps within a level. The classes converge to two $3$-adic integers.
-- source:
--   Beaver Math Olympiad problem 5 (machine 1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_---0RE). Companion of BMO5.three_adic_uniqueness; original result of this submission.

import Mathlib

namespace BMO5
theorem three_adic_existence (k r : ℕ) (hr : r < 2) :
    ∃ i, i % 2 = r ∧ 3 ^ k ∣ 20 * 2 ^ i + i + 1 := by
  sorry
end BMO5
