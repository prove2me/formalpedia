-- Prove2me | Theorems.Thm_BMO5_adm_count
-- name    : BMO5.adm_count
-- status  : Proved
-- author  : @alon yuval
-- created : 2026-11-23T17:25:18.925105+00:00
-- url     : https://prove2.me/theorems/9d8ce6fd-6156-440b-a4ec-cd3169f9a134
-- title:
--   BMO #5: at most $2^{D+1}$ admissible halting levels mod $2\cdot 3^D$
-- statement:
--   Write $N_i = 20\cdot 2^i + i + 1$ (the halting value of $c = 2b + a + 5$ at level $i$). $\mathrm{adm}(D, i)$ holds iff there is a sequence of $D$ backward blocks, each either *T* (undo a tripling) or *ST* (undo a subtraction from level $i - \delta - 1$, then a tripling), such that every undone tripling is integral. In formulas: starting from $F = N_i$, $m = \delta = 0$, block T needs $3^{m+1} \mid F$; block ST replaces $F$ by $F + 3^m(20\cdot 2^{i-\delta-1} - 3)$, increments $\delta$, and needs $3^{m+1} \mid F$; each block increments $m$.
--
--   **Theorem.** Among the residues $r < 2\cdot 3^D$, at most $2^{D+1}$ are admissible (tested via the representative $r + 2\cdot 3^D(D+1)$). Computation shows exactly $2^{D+1}$ for $D \le 6$.
--
--   Proof idea (3-adic): if $3^m \mid F$, then shifting $i$ by $2\cdot 3^m t$ changes $F$ by $2\cdot 3^m t$ modulo $3^{m+1}$, because $4^{3^m} \equiv 1 \pmod{3^{m+1}}$. So the new $3$-adic digit $t$ of $i$ sweeps $F/3^m \bmod 3$. Block T needs residue $0$ and block ST needs residue $-20\cdot 2^{j-1} \not\equiv 0$, so each admissible class has at most two admissible lifts. That gives $2 \cdot 2^D$ classes.
-- source:
--   Beaver Math Olympiad problem 5 (machine 1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_---0RE), https://wiki.bbchallenge.org/wiki/Beaver_Math_Olympiad. Original result of this submission; builds on BMO5.level_halt_dvd, BMO5.three_adic_uniqueness, BMO5.halt_level_mod18.

import Mathlib
import Definitions.Def_BMO5Adm

namespace BMO5
theorem adm_count (D : ℕ) :
    ((Finset.range (2 * 3 ^ D)).filter (fun r => BMO5Adm.adm D (r + 2 * 3 ^ D * (D + 1)) = true)).card ≤ 2 ^ (D + 1) := by
  sorry
end BMO5
