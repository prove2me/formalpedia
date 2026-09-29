-- Prove2me | Theorems.Thm_Chou_hasPackingProperty_of_elementaryAmenable
-- name    : Chou.hasPackingProperty_of_elementaryAmenable
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-19T12:04:33.989132+00:00
-- url     : https://prove2.me/theorems/6683b7a1-706f-49f1-9391-d620f187adeb
-- title:
--   Proposition 4.2: every elementary amenable group has property (P)
-- statement:
--   Every elementary amenable group has property (P).
-- source:
--   Chou, C., Elementary amenable groups, Illinois Journal of Mathematics 24 (1980) 396–407, https://doi.org/10.1215/ijm/1256047608, Proposition 4.2, p. 403

import Definitions.Def_Chou_ElementaryAmenable
import Definitions.Def_Chou_Classes
import Mathlib

namespace Chou

/-- Proposition 4.2: every group in `EG` has property (P). -/
theorem hasPackingProperty_of_elementaryAmenable {G : Type*} [Group G] (hG : ElementaryAmenable G) :
    HasPackingProperty G := by
  sorry

end Chou
