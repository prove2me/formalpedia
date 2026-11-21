-- Prove2me | Theorems.Thm_CollatzMission_syracuse_descent_large_three_mod_four
-- name    : CollatzMission.syracuse_descent_large_three_mod_four
-- status  : Open
-- author  : @yuzhou
-- created : 2026-11-20T10:28:07.656206+00:00
-- url     : https://prove2.me/theorems/1a072104-f400-497f-9e95-939aa0eb2ca0
-- title:
--   Syracuse descent for large inputs congruent to three modulo four
-- statement:
--   Let $T(n)$ be the odd part of $3n+1$. For each $n\ge 2{,}310{,}000$ with $n\equiv 3\pmod{4}$, does some Syracuse iterate $T^t(n)$ fall strictly below $n$? This is the remaining descent case after applying the platform’s finite descent bound below $2{,}310{,}000$ and the one-step bound $T(n)\le (3n+1)/4<n$ when $n>1$ and $n\equiv 1\pmod{4}$.
-- source:
--   Descent subproblem for CollatzMission.syracuse_odd_conjecture, with cutoff from syracuse_descends_below_2310000.

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate

theorem CollatzMission.syracuse_descent_large_three_mod_four
    (n : ℕ) (hn : 2310000 ≤ n) (hmod : n % 4 = 3) :
    ∃ t : ℕ, syracuseStep^[t] n < n := by sorry
