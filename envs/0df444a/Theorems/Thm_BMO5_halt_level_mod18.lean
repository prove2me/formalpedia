-- Prove2me | Theorems.Thm_BMO5_halt_level_mod18
-- name    : BMO5.halt_level_mod18
-- status  : Proved
-- author  : @alon yuval
-- created : 2026-11-23T17:03:32.367807+00:00
-- url     : https://prove2.me/theorems/1cc929ea-436e-461e-a7c2-f7cc0adf1445
-- title:
--   BMO #5 can only halt at levels $a_n \bmod 18 \in \{2,5,6,7,8,11,12,13\}$
-- statement:
--   Let $f(x) = 10\cdot 2^x - 1$, $(a_0,b_0) = (0,5)$, and $(a_{n+1},b_{n+1}) = (a_n+1, b_n - f(a_n))$ if $b_n \ge f(a_n)$, otherwise $(a_n, 3b_n + a_n + 5)$ (Beaver Math Olympiad problem 5; the machine halts iff $b_n = f(a_n) - 1$).
--
--   **Theorem.** If $b_n = f(a_n) - 1$ then $a_n \bmod 18 \in \{2,5,6,7,8,11,12,13\}$.
--
--   This strengthens `BMO5.no_halt_level_mod6` (which leaves 12 of the 18 classes) to 8 of 18 classes. The proof traces a halting state back through its last two to four steps. Each admissible pattern of triplings (T) and subtractions (S), namely TT, TST, TTS and TSTS, forces a congruence modulo $9$ via $2^i \bmod 9$. The patterns SS, SST and SSTS are excluded by the invariant $2b_n + a_n + 5 < 3(20\cdot 2^{a_n} + a_n + 3)$, and the first four states are checked directly.
-- source:
--   Beaver Math Olympiad problem 5 (machine 1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_---0RE), https://wiki.bbchallenge.org/wiki/Beaver_Math_Olympiad. Original result of this submission.

import Mathlib

namespace BMO5
theorem halt_level_mod18 (a b : ℕ → ℕ) (a_ini : a 0 = 0) (b_ini : b 0 = 5)
    (a_rec : ∀ n, a (n + 1) = if 10 * 2 ^ (a n) - 1 ≤ b n then a n + 1 else a n)
    (b_rec : ∀ n, b (n + 1) = if 10 * 2 ^ (a n) - 1 ≤ b n then b n - (10 * 2 ^ (a n) - 1)
      else 3 * b n + a n + 5) :
    ∀ n, b n = 10 * 2 ^ (a n) - 2 →
      (a n % 18 = 2 ∨ a n % 18 = 5 ∨ a n % 18 = 6 ∨ a n % 18 = 7 ∨ a n % 18 = 8 ∨
       a n % 18 = 11 ∨ a n % 18 = 12 ∨ a n % 18 = 13) := by
  sorry
end BMO5
