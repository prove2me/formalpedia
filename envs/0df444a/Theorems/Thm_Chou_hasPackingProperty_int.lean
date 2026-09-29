-- Prove2me | Theorems.Thm_Chou_hasPackingProperty_int
-- name    : Chou.hasPackingProperty_int
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-19T12:02:35.733447+00:00
-- url     : https://prove2.me/theorems/5faea433-5f06-4df6-b1dd-1da800d6ea71
-- title:
--   $\mathbb Z$ has property (P)
-- statement:
--   The additive group of integers (written multiplicatively) has property (P).
-- source:
--   Chou, C., Elementary amenable groups, Illinois Journal of Mathematics 24 (1980) 396–407, https://doi.org/10.1215/ijm/1256047608, p. 403

import Definitions.Def_Chou_ElementaryAmenable
import Definitions.Def_Chou_Classes
import Mathlib

namespace Chou

/-- p. 403: the additive group of integers has property (P). -/
theorem hasPackingProperty_int : HasPackingProperty (Multiplicative ℤ) := by
  sorry

end Chou
