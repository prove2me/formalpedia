-- Prove2me | Theorems.Thm_Chou_hasPackingProperty_of_commGroup_of_fg
-- name    : Chou.hasPackingProperty_of_commGroup_of_fg
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-19T12:03:05.523015+00:00
-- url     : https://prove2.me/theorems/3474a1f5-892a-4ef7-96cb-998c284d09de
-- title:
--   Finitely generated abelian groups have property (P)
-- statement:
--   Every finitely generated abelian group has property (P).
-- source:
--   Chou, C., Elementary amenable groups, Illinois Journal of Mathematics 24 (1980) 396–407, https://doi.org/10.1215/ijm/1256047608, p. 403 ("A similar construction shows that every finitely generated abelian group has property (P)")

import Definitions.Def_Chou_ElementaryAmenable
import Definitions.Def_Chou_Classes
import Mathlib

namespace Chou

/-- p. 403: every finitely generated abelian group has property (P). -/
theorem hasPackingProperty_of_commGroup_of_fg {G : Type*} [CommGroup G] [Group.FG G] : HasPackingProperty G := by
  sorry

end Chou
