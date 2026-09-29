-- Prove2me | Theorems.Thm_Chou_isVirtuallyNilpotent_or_hasFreeSubsemigroupOfRankTwo_of_elementaryAmenable
-- name    : Chou.isVirtuallyNilpotent_or_hasFreeSubsemigroupOfRankTwo_of_elementaryAmenable
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-19T12:01:37.506105+00:00
-- url     : https://prove2.me/theorems/6124b4b3-017e-42a4-ac1f-eb3014dc4976
-- title:
--   Theorem 3.2′: finitely generated elementary amenable groups are almost nilpotent or contain a free subsemigroup on two generators
-- statement:
--   A finitely generated elementary amenable group has a nilpotent subgroup of finite index, or
--   contains two elements generating a free subsemigroup.
-- source:
--   Chou, C., Elementary amenable groups, Illinois Journal of Mathematics 24 (1980) 396–407, https://doi.org/10.1215/ijm/1256047608, Theorem 3.2′, p. 401

import Definitions.Def_Chou_ElementaryAmenable
import Definitions.Def_Chou_Growth
import Mathlib

namespace Chou

/-- Theorem 3.2′: a finitely generated group in `EG` is almost nilpotent or contains a free
subsemigroup on two generators. -/
theorem isVirtuallyNilpotent_or_hasFreeSubsemigroupOfRankTwo_of_elementaryAmenable {G : Type*} [Group G] [Group.FG G] (hG : ElementaryAmenable G) :
    Group.IsVirtuallyNilpotent G ∨ HasFreeSubsemigroupOfRankTwo G := by
  sorry

end Chou
