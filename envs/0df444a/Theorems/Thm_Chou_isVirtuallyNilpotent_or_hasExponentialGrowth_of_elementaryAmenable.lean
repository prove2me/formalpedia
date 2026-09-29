-- Prove2me | Theorems.Thm_Chou_isVirtuallyNilpotent_or_hasExponentialGrowth_of_elementaryAmenable
-- name    : Chou.isVirtuallyNilpotent_or_hasExponentialGrowth_of_elementaryAmenable
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-19T12:00:36.781149+00:00
-- url     : https://prove2.me/theorems/9fbe8259-8938-413e-8bc2-22b08faf9ade
-- title:
--   Theorem 3.2: finitely generated elementary amenable groups are almost nilpotent or of exponential growth
-- statement:
--   A finitely generated elementary amenable group has a nilpotent subgroup of finite index, or
--   has exponential growth.
-- source:
--   Chou, C., Elementary amenable groups, Illinois Journal of Mathematics 24 (1980) 396–407, https://doi.org/10.1215/ijm/1256047608, Theorem 3.2, p. 400

import Definitions.Def_Chou_ElementaryAmenable
import Definitions.Def_Chou_Growth
import Mathlib

namespace Chou

/-- Theorem 3.2: a finitely generated group in `EG` is almost nilpotent or has exponential
growth. -/
theorem isVirtuallyNilpotent_or_hasExponentialGrowth_of_elementaryAmenable {G : Type*} [Group G] [Group.FG G] (hG : ElementaryAmenable G) :
    Group.IsVirtuallyNilpotent G ∨ HasExponentialGrowth G := by
  sorry

end Chou
