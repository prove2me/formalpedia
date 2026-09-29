-- Prove2me | Theorems.Thm_Chou_hasPackingProperty_freeGroup
-- name    : Chou.hasPackingProperty_freeGroup
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-19T13:16:27.19839+00:00
-- url     : https://prove2.me/theorems/fe93b9aa-0b3f-4e24-98a8-91ff5c38c02f
-- title:
--   Free groups have property (P)
-- statement:
--   Every free group has property (P).
-- source:
--   Chou, C., Elementary amenable groups, Illinois Journal of Mathematics 24 (1980) 396–407, https://doi.org/10.1215/ijm/1256047608, p. 406

import Definitions.Def_Chou_ElementaryAmenable
import Definitions.Def_Chou_Classes
import Mathlib

namespace Chou

/-- p. 406: every free group has property (P). -/
theorem hasPackingProperty_freeGroup (α : Type*) : HasPackingProperty (FreeGroup α) := by
  sorry

end Chou
