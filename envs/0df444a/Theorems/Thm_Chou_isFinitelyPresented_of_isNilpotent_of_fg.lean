-- Prove2me | Theorems.Thm_Chou_isFinitelyPresented_of_isNilpotent_of_fg
-- name    : Chou.isFinitelyPresented_of_isNilpotent_of_fg
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-19T11:58:50.504677+00:00
-- url     : https://prove2.me/theorems/28e1ea30-27d1-4636-9d4c-c042868e4eef
-- title:
--   Finitely generated nilpotent groups are finitely presented (external)
-- statement:
--   A finitely generated nilpotent group is finitely presented.
-- source:
--   Chou, C., Elementary amenable groups, Illinois Journal of Mathematics 24 (1980) 396–407, https://doi.org/10.1215/ijm/1256047608, p. 400 ("C₁ is also finitely generated and hence is finitely presented")

import Mathlib

namespace Chou

/-- p. 400 (external): a finitely generated nilpotent group is finitely presented. -/
theorem isFinitelyPresented_of_isNilpotent_of_fg {G : Type*} [Group G] [Group.FG G] [Group.IsNilpotent G] :
    Group.IsFinitelyPresented G := by
  sorry

end Chou
