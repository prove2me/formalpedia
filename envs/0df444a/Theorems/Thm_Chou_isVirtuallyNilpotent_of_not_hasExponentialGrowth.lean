-- Prove2me | Theorems.Thm_Chou_isVirtuallyNilpotent_of_not_hasExponentialGrowth
-- name    : Chou.isVirtuallyNilpotent_of_not_hasExponentialGrowth
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-09-21T15:34:25.498087+00:00
-- url     : https://prove2.me/theorems/6a7da0f8-a96a-4409-9427-32980df6d56c
-- title:
--   Finitely generated solvable groups without exponential growth are virtually nilpotent
-- statement:
--   A finitely generated solvable group without exponential growth is virtually nilpotent (has a nilpotent subgroup of finite index).

import Definitions.Def_Chou_Growth
import Mathlib

namespace Chou

theorem isVirtuallyNilpotent_of_not_hasExponentialGrowth {G : Type*} [Group G] [Group.FG G] [Group.IsSolvable G] (h : ¬ HasExponentialGrowth G) : Group.IsVirtuallyNilpotent G := by sorry

end Chou
