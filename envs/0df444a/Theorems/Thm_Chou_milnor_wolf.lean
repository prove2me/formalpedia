-- Prove2me | Theorems.Thm_Chou_milnor_wolf
-- name    : Chou.milnor_wolf
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-19T11:58:12.277889+00:00
-- url     : https://prove2.me/theorems/705f6bd5-7ff8-4e26-a124-299bcf1614ff
-- title:
--   Milnor–Wolf: exponentially bounded solvable groups are almost nilpotent (external)
-- statement:
--   A finitely generated solvable group which is exponentially bounded has a nilpotent subgroup
--   of finite index.
-- source:
--   Chou, C., Elementary amenable groups, Illinois Journal of Mathematics 24 (1980) 396–407, https://doi.org/10.1215/ijm/1256047608, p. 399 (Milnor [17], Wolf [22], cited)

import Definitions.Def_Chou_Growth
import Mathlib

namespace Chou

/-- Milnor–Wolf (p. 399, external): a finitely generated solvable group which is exponentially
bounded is almost nilpotent. -/
theorem milnor_wolf {G : Type*} [Group G] [Group.FG G] [Group.IsSolvable G] (h : IsExponentiallyBounded G) :
    Group.IsVirtuallyNilpotent G := by
  sorry

end Chou
