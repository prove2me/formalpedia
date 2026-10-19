-- Prove2me | Theorems.Thm_AngelDevil_niceAngelWins_of_wall_no_return
-- name    : AngelDevil.niceAngelWins_of_wall_no_return
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-18T14:13:53.247026+00:00
-- url     : https://prove2.me/theorems/3ec0f8c7-bca2-454f-9f1f-e43728a98359
-- title:
--   No-return of the wall trace implies the Nice Angel theorem
-- statement:
--   Assume that against every Nice Devil, the specified two-transition wall trace never returns to its initial directed wall at a positive index. Then there is one power-two Angel strategy that survives against every Nice Devil and, against each such Devil, leaves every finite box centered at the origin. The no-return premise is an explicit geometric assumption; this conditional theorem does not by itself establish that premise.
-- source:
--   Mathe, The Angel of power 2 wins (2007), https://doi.org/10.1017/S0963548306008303; author manuscript pp. 6-8, octagonal wall-following rule, Claim 3.1 analogue, Proposition 4.3 and Theorem 4.5. Two wall transitions per turn give an admissible power-two implementation; no-return is the remaining geometric obligation.

import Definitions.Def_AngelDevil_WallWalk

theorem AngelDevil.niceAngelWins_of_wall_no_return (hreturn : ∀ D, AngelDevil.Nice 2 D → ∀ n, 0 < n → AngelDevil.wallTrace D n ≠ AngelDevil.initialWall) : AngelDevil.NiceAngelWins 2 := by sorry
