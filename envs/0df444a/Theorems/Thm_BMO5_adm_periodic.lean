-- Prove2me | Theorems.Thm_BMO5_adm_periodic
-- name    : BMO5.adm_periodic
-- status  : Proved
-- author  : @alon yuval
-- created : 2026-11-23T17:25:16.275711+00:00
-- url     : https://prove2.me/theorems/e8d794ad-b416-4331-8a48-0c02c950eb23
-- title:
--   BMO #5: block admissibility depends only on the level mod $2\cdot 3^D$
-- statement:
--   Write $N_i = 20\cdot 2^i + i + 1$ (the halting value of $c = 2b + a + 5$ at level $i$). $\mathrm{adm}(D, i)$ holds iff there is a sequence of $D$ backward blocks, each either *T* (undo a tripling) or *ST* (undo a subtraction from level $i - \delta - 1$, then a tripling), such that every undone tripling is integral. In formulas: starting from $F = N_i$, $m = \delta = 0$, block T needs $3^{m+1} \mid F$; block ST replaces $F$ by $F + 3^m(20\cdot 2^{i-\delta-1} - 3)$, increments $\delta$, and needs $3^{m+1} \mid F$; each block increments $m$.
--
--   **Theorem.** If $i, j \ge D + 1$ and $i \equiv j \pmod{2\cdot 3^D}$, then $\mathrm{adm}(D,i) = \mathrm{adm}(D,j)$.
--
--   Reason: the checks only involve $F$ modulo $3^{m+1}$ with $m < D$. There $i$ enters linearly (period $3^D$) and through powers $2^{i-\delta}$ (period $2\cdot 3^{D-1}$ modulo $3^D$).
-- source:
--   Beaver Math Olympiad problem 5 (machine 1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_---0RE), https://wiki.bbchallenge.org/wiki/Beaver_Math_Olympiad. Original result of this submission; builds on BMO5.level_halt_dvd, BMO5.three_adic_uniqueness, BMO5.halt_level_mod18.

import Mathlib
import Definitions.Def_BMO5Adm

namespace BMO5
theorem adm_periodic (D i j : ℕ) (hi : D + 1 ≤ i) (hj : D + 1 ≤ j)
    (h : i % (2 * 3 ^ D) = j % (2 * 3 ^ D)) : BMO5Adm.adm D i = BMO5Adm.adm D j := by
  sorry
end BMO5
