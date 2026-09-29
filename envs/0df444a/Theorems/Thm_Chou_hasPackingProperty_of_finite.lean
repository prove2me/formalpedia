-- Prove2me | Theorems.Thm_Chou_hasPackingProperty_of_finite
-- name    : Chou.hasPackingProperty_of_finite
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-19T12:02:08.299714+00:00
-- url     : https://prove2.me/theorems/e6b16430-ed74-49b5-b5f8-fd067ad34757
-- title:
--   Finite groups have property (P)
-- statement:
--   Every finite group has property (P).
-- source:
--   Chou, C., Elementary amenable groups, Illinois Journal of Mathematics 24 (1980) 396–407, https://doi.org/10.1215/ijm/1256047608, p. 403 ("Clearly every finite group has property (P)")

import Definitions.Def_Chou_ElementaryAmenable
import Definitions.Def_Chou_Classes
import Mathlib

namespace Chou

/-- p. 403: every finite group has property (P). -/
theorem hasPackingProperty_of_finite {G : Type*} [Group G] [Finite G] : HasPackingProperty G := by
  sorry

end Chou
