-- Prove2me | Theorems.Thm_BMO5_adm_of_halt
-- name    : BMO5.adm_of_halt
-- status  : Open
-- author  : @alon yuval
-- created : 2026-11-23T17:25:24.498798+00:00
-- url     : https://prove2.me/theorems/11a57ce7-f2b1-4f48-8457-cbfe93c22f30
-- title:
--   BMO #5: a halt at a high level forces the backward block condition
-- statement:
--   Let $f(x) = 10\cdot 2^x - 1$, $(a_0,b_0) = (0,5)$, and $(a_{n+1},b_{n+1}) = (a_n+1, b_n - f(a_n))$ if $b_n \ge f(a_n)$, otherwise $(a_n, 3b_n + a_n + 5)$ (Beaver Math Olympiad problem 5; the machine halts iff $b_n = f(a_n) - 1$).
--
--   Write $N_i = 20\cdot 2^i + i + 1$ (the halting value of $c = 2b + a + 5$ at level $i$). $\mathrm{adm}(D, i)$ holds iff there is a sequence of $D$ backward blocks, each either *T* (undo a tripling) or *ST* (undo a subtraction from level $i - \delta - 1$, then a tripling), such that every undone tripling is integral. In formulas: starting from $F = N_i$, $m = \delta = 0$, block T needs $3^{m+1} \mid F$; block ST replaces $F$ by $F + 3^m(20\cdot 2^{i-\delta-1} - 3)$, increments $\delta$, and needs $3^{m+1} \mid F$; each block increments $m$.
--
--   **Theorem.** For every $D$ there is $i_0$ such that if the machine halts at step $n$ with $a_n \ge i_0$, then $\mathrm{adm}(D, a_n)$ holds.
--
--   Idea: read the real orbit backwards from the halt. The invariant $2b + a + 5 < 3(20\cdot 2^a + a + 3)$ shows that two consecutive subtractions leave a value below $a + 4$, after which about $a\log_3 2$ triplings are needed. So for $a_n\ge i_0(D)$ the last $D$ blocks are of type T or ST, and each undone tripling is integral because the earlier states are integers.
-- source:
--   Beaver Math Olympiad problem 5 (machine 1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_---0RE), https://wiki.bbchallenge.org/wiki/Beaver_Math_Olympiad. Original result of this submission; builds on BMO5.level_halt_dvd, BMO5.three_adic_uniqueness, BMO5.halt_level_mod18.

import Mathlib
import Definitions.Def_BMO5Adm

namespace BMO5
theorem adm_of_halt (a b : ℕ → ℕ) (a_ini : a 0 = 0) (b_ini : b 0 = 5)
    (a_rec : ∀ n, a (n + 1) = if 10 * 2 ^ (a n) - 1 ≤ b n then a n + 1 else a n)
    (b_rec : ∀ n, b (n + 1) = if 10 * 2 ^ (a n) - 1 ≤ b n then b n - (10 * 2 ^ (a n) - 1)
      else 3 * b n + a n + 5) :
    ∀ D, ∃ i0, ∀ n, b n = 10 * 2 ^ (a n) - 2 → i0 ≤ a n → BMO5Adm.adm D (a n) = true := by
  sorry
end BMO5
