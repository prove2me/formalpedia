-- Prove2me | Theorems.Thm_AngelDevil_wallTrace_never_returns
-- name    : AngelDevil.wallTrace_never_returns
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-18T14:13:50.772574+00:00
-- url     : https://prove2.me/theorems/775a4edf-d28a-4a62-89b2-2c5de5c2feaf
-- title:
--   Geometric no-return for the power-two wall trace
-- statement:
--   Against every Nice Devil of power two, the specified boundary-walking strategy never encounters its initial directed wall at any positive wall-transition index. The initial wall is the east side of square (-1,0). The trace uses two wall transitions per Angel turn and the obstacle set after that turn's Devil move. This is the geometric no-return obligation underlying the escape argument; it does not assume non-repetition or escape.
-- source:
--   Mathe, The Angel of power 2 wins (2007), https://doi.org/10.1017/S0963548306008303; author manuscript pp. 6-8, octagonal wall-following rule, Claim 3.1 analogue, Proposition 4.3 and Theorem 4.5. Two wall transitions per turn give an admissible power-two implementation; no-return is the remaining geometric obligation.

import Definitions.Def_AngelDevil_WallWalk

theorem AngelDevil.wallTrace_never_returns (D : AngelDevil.DevilStrategy) (hnice : AngelDevil.Nice 2 D) (n : Nat) (hn : 0 < n) : AngelDevil.wallTrace D n ≠ AngelDevil.initialWall := by sorry
